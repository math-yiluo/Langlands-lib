import Langlands.Geometry.Building.RootReflectionStatement
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.RootSubgroupSeparation
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj commutatorElement Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace RootReflectionProof

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}

theorem eval_zsmul_char (m : ℤ) (a : characterLattice S) (v : V S) :
    eval S (m • a) v = m * eval S a v := by
  rw [eval_eq_pair, eval_eq_pair, TensorProduct.tmul_smul, map_zsmul, LinearMap.smul_apply,
    zsmul_eq_mul]

theorem eval_comb (m : ℤ) (n : ℕ) (a b : characterLattice S) (v : V S) :
    eval S (m • a + n • b) v = m * eval S a v + n * eval S b v := by
  rw [eval_add_char, eval_zsmul_char, eval_nsmul_char]

theorem pairing_comb (m : ℤ) (n : ℕ) (a b : characterLattice S) (ν : cocharacterLattice S) :
    latticePairing S (m • a + n • b) ν = m * latticePairing S a ν + n * latticePairing S b ν := by
  simp [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply]

/-- The side condition of V 3 holds when the two characters are separated by a real
cocharacter: `b(w) < 0 ≤ ... ` excludes `b ∈ -ℝ_{>0} a` as soon as `a(w) ≤ 0`. -/
theorem not_mem_neg_ray {a b : characterLattice S} {w : V S} (hb : eval S b w < 0)
    (ha : eval S a w ≤ 0) :
    ∀ t : ℝ, 0 < t → ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a) := by
  intro t ht h
  have h' := congrArg (fun z => pair S z w) h
  simp only [map_neg, map_smul, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul] at h'
  rw [← LinearMap.congr_fun (eval_eq_pair S b) w, ← LinearMap.congr_fun (eval_eq_pair S a) w]
    at h'
  nlinarith

/-- Selection of an extremal root (internal; replaces KP's choice of an ordering). Among the
roots `d` with `d(w) < 0`, take one minimizing `⟨d, ν⟩ / (-d(w))`, and among those one
maximizing `-d(w)`. Then every root `m a + n τ` with `n ≥ 1` is `τ` itself (`m = 0, n = 1`)
or has `m > 0`. -/
theorem exists_extremal_root {Φ : Set (characterLattice S)} (hfin : Φ.Finite)
    {a : characterLattice S} {ν : cocharacterLattice S} (hν : latticePairing S a ν = 2)
    {w : V S} (haw : eval S a w = 0) {b : characterLattice S} (hb : b ∈ Φ)
    (hbw : eval S b w < 0) :
    ∃ τ ∈ Φ, eval S τ w < 0 ∧ ∀ (m : ℤ) (n : ℕ), 0 < n → m • a + n • τ ∈ Φ →
      (m = 0 ∧ n = 1) ∨ 0 < m := by
  classical
  let C := hfin.toFinset.filter (fun d => eval S d w < 0)
  have hbC : b ∈ C := Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hb, hbw⟩
  let ρ : characterLattice S → ℝ := fun d => (latticePairing S d ν : ℝ) / (-eval S d w)
  obtain ⟨τ₀, hτ₀C, hτ₀⟩ := C.exists_min_image ρ ⟨b, hbC⟩
  let C' := C.filter (fun d => ρ d = ρ τ₀)
  have hτ₀C' : τ₀ ∈ C' := Finset.mem_filter.2 ⟨hτ₀C, rfl⟩
  obtain ⟨τ, hτC', hτ⟩ := C'.exists_max_image (fun d => -eval S d w) ⟨τ₀, hτ₀C'⟩
  obtain ⟨hτC, hρτ⟩ := Finset.mem_filter.1 hτC'
  obtain ⟨hτΦ, hτw⟩ := Finset.mem_filter.1 hτC
  refine ⟨τ, hfin.mem_toFinset.1 hτΦ, hτw, fun m n hn hd => ?_⟩
  have hdw : eval S (m • a + n • τ) w = n * eval S τ w := by
    rw [eval_comb, haw]; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < -eval S τ w := by linarith
  have hnc : 0 < -(n * eval S τ w) := by nlinarith
  have hdC : m • a + n • τ ∈ C :=
    Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 hd, by rw [hdw]; nlinarith⟩
  have hρd : ρ (m • a + n • τ) =
      ((m : ℝ) * 2 + n * latticePairing S τ ν) / (-(n * eval S τ w)) := by
    simp only [ρ, pairing_comb, hν, hdw]
    push_cast
    ring
  have hmin := hτ₀ _ hdC
  rw [← hρτ, hρd] at hmin
  change (latticePairing S τ ν : ℝ) / (-eval S τ w) ≤ _ at hmin
  rw [div_le_div_iff₀ hc hnc] at hmin
  have hm : (0 : ℝ) ≤ m := by nlinarith
  have hm' : 0 ≤ m := by exact_mod_cast hm
  rcases hm'.lt_or_eq with hm0 | hm0
  · exact Or.inr hm0
  · subst hm0
    refine Or.inl ⟨rfl, ?_⟩
    have hdC' : (0 : ℤ) • a + n • τ ∈ C' := by
      refine Finset.mem_filter.2 ⟨hdC, ?_⟩
      rw [hρd, ← hρτ]
      change _ = (latticePairing S τ ν : ℝ) / (-eval S τ w)
      rw [div_eq_div_iff hnc.ne' hc.ne']
      push_cast
      ring
    have hmax := hτ _ hdC'
    simp only [hdw] at hmax
    have : (n : ℝ) ≤ 1 := by nlinarith
    exact le_antisymm (by exact_mod_cast this) hn

/-- A separating cocharacter (internal). If `a(w) = 0 > τ(w)` and `⟨a, ν⟩ = 2`, some
cocharacter `λ` pairs negatively with `τ` and positively with every `m a + n τ ∈ Φ`, `m > 0`. -/
theorem exists_separating_cocharacter (hS : IsSplitTorus S.toGrp) {Φ : Set (characterLattice S)}
    (hfin : Φ.Finite) {a : characterLattice S} {ν : cocharacterLattice S}
    (hν : latticePairing S a ν = 2) {w : V S} (haw : eval S a w = 0) {τ : characterLattice S}
    (hτw : eval S τ w < 0) :
    ∃ lam : cocharacterLattice S, latticePairing S τ lam < 0 ∧
      ∀ (m : ℤ) (n : ℕ), 0 < m → m • a + n • τ ∈ Φ → 0 < latticePairing S (m • a + n • τ) lam := by
  set T := latticePairing S τ ν with hT
  have hχ : (2 : ℤ) • τ + (-T) • a ≠ 0 := by
    intro h
    have h' := congrArg (fun c => eval S c w) h
    simp only [eval_add_char, eval_zsmul_char, haw, eval_zero_char] at h'
    push_cast at h'
    linarith
  obtain ⟨D, hD, ζ, hζ⟩ := hS.exists_pairing_eq_pos hχ
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hζ
  set ζ₀ := (2 : ℤ) • ζ + (-latticePairing S a ζ) • ν with hζ₀
  have h1 : latticePairing S a ζ₀ = 0 := by
    simp only [hζ₀, map_add, map_zsmul, smul_eq_mul, hν]
    ring
  have h2 : latticePairing S τ ζ₀ = D := by
    simp only [hζ₀, map_add, map_zsmul, smul_eq_mul, ← hT]
    linear_combination hζ
  obtain ⟨R, hR⟩ := (hfin.image fun d => -eval S d w).bddAbove
  obtain ⟨K, hK⟩ := exists_nat_gt (R / (-eval S τ w))
  set lam := (-(K : ℤ) * T - 1) • ζ₀ + ((D : ℤ) * K) • ν with hlam
  have h3 : latticePairing S a lam = 2 * D * K := by
    simp only [hlam, map_add, map_zsmul, smul_eq_mul, h1, hν]
    ring
  have h4 : latticePairing S τ lam = -D := by
    simp only [hlam, map_add, map_zsmul, smul_eq_mul, h2, ← hT]
    ring
  refine ⟨lam, by rw [h4]; exact_mod_cast Int.neg_neg_of_pos (by exact_mod_cast hD), ?_⟩
  intro m n hm hd
  have hdR : -eval S (m • a + n • τ) w ≤ R := hR ⟨_, hd, rfl⟩
  rw [eval_comb, haw] at hdR
  have hc : 0 < -eval S τ w := by linarith
  have hnK : (n : ℝ) < K := by
    rw [div_lt_iff₀ hc] at hK
    nlinarith
  have hnK' : (n : ℤ) < K := by exact_mod_cast hnK
  rw [pairing_comb, h3, h4]
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have : (0 : ℤ) < 2 * K * m - n := by nlinarith
  nlinarith [mul_pos hD' this]

/-! ### Conjugation and normalizers of generated subgroups -/

section Normalizer

variable {M : Type*} [Group M]

theorem conj_mem_of_forall_mem {X : Set M} {H : Subgroup M} {c : M}
    (h : ∀ x ∈ X, c * x * c⁻¹ ∈ H) {y : M} (hy : y ∈ Subgroup.closure X) : c * y * c⁻¹ ∈ H := by
  have : Subgroup.closure X ≤ H.comap (MulAut.conj c).toMonoidHom :=
    (Subgroup.closure_le _).2 fun x hx => by simpa [MulAut.conj_apply] using h x hx
  simpa [MulAut.conj_apply] using this hy

theorem mem_normalizer_closure {X : Set M} {c : M}
    (h₁ : ∀ x ∈ X, c * x * c⁻¹ ∈ Subgroup.closure X)
    (h₂ : ∀ x ∈ X, c⁻¹ * x * c ∈ Subgroup.closure X) :
    c ∈ Subgroup.normalizer (Subgroup.closure X : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_of_forall_mem h₁, fun hy => ?_⟩
  have := conj_mem_of_forall_mem (c := c⁻¹) (by simpa using h₂) hy
  simpa [mul_assoc] using this

theorem conj_eq_commutator_mul (c x : M) : c * x * c⁻¹ = ⁅c, x⁆ * x := by
  rw [commutatorElement_def]
  group

end Normalizer

/-! ### Subgroups generated by filtration pieces along `ℤ a + ℕ τ` -/

section Generators

variable {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]

variable (i) in
/-- The union of the filtration pieces `U_{m a + n τ, φ, n t}` for `n > 0` and `P m`. -/
def gens (φ : RootFunctionFamily S G) (a τ : characterLattice S) (t : ℝ) (P : ℤ → Prop) :
    Set (rationalPoints G) :=
  ⋃ (m : ℤ) (n : ℕ) (_ : 0 < n) (_ : P m) (_ : m • a + n • τ ∈ relativeRoots i),
    rootFiltration i φ (m • a + n • τ) (n * t)

theorem subset_gens {φ : RootFunctionFamily S G} {a τ : characterLattice S} {t : ℝ}
    {P : ℤ → Prop} {m : ℤ} {n : ℕ} (hn : 0 < n) (hm : P m)
    (hd : m • a + n • τ ∈ relativeRoots i) :
    rootFiltration i φ (m • a + n • τ) (n * t) ⊆ gens i φ a τ t P := by
  intro x hx
  simp only [gens, Set.mem_iUnion]
  exact ⟨m, n, hn, hm, hd, hx⟩

theorem mem_gens {φ : RootFunctionFamily S G} {a τ : characterLattice S} {t : ℝ}
    {P : ℤ → Prop} {x : rationalPoints G} :
    x ∈ gens i φ a τ t P ↔ ∃ (m : ℤ) (n : ℕ), 0 < n ∧ P m ∧ m • a + n • τ ∈ relativeRoots i ∧
      x ∈ rootFiltration i φ (m • a + n • τ) (n * t) := by
  simp only [gens, Set.mem_iUnion, exists_prop]

variable [Mono i.hom.hom.left] {φ : RootFunctionFamily S G}

/-- One application of V 3 lands in the subgroup generated by `gens`, when every positive
combination `p a' + q (m a + n τ)` is again of the indexed form. -/
theorem commutator_le_closure_gens (hφ : IsRootDatumValuation i φ) {a τ a' : characterLattice S}
    {t r : ℝ} {P : ℤ → Prop} (ha' : a' ∈ relativeRoots i) {w : V S} (haw : eval S a w = 0)
    (hτw : eval S τ w < 0) (ha'w : eval S a' w ≤ 0) {m : ℤ} {n : ℕ} (hn : 0 < n)
    (hd : m • a + n • τ ∈ relativeRoots i)
    (hstep : ∀ p q : ℕ, 0 < p → 0 < q → ∃ (m' : ℤ) (n' : ℕ), 0 < n' ∧ P m' ∧
      p • a' + q • (m • a + n • τ) = m' • a + n' • τ ∧
      (p * r + q * (n * t) : ℝ) = n' * t) :
    ⁅Subgroup.closure (rootFiltration i φ a' r),
      Subgroup.closure (rootFiltration i φ (m • a + n • τ) (n * t))⁆ ≤
      Subgroup.closure (gens i φ a τ t P) := by
  have hdw : eval S (m • a + n • τ) w < 0 := by
    rw [eval_comb, haw]
    have : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith
  refine (hφ.commutator a' ha' _ hd (not_mem_neg_ray hdw ha'w) r (n * t)).trans ?_
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨p, q, hp, hq, hpq, hx⟩ := hx
  obtain ⟨m', n', hn', hm', he, hr⟩ := hstep p q hp hq
  rw [he] at hpq hx
  rw [hr] at hx
  exact Subgroup.subset_closure (subset_gens hn' hm' hpq hx)

/-- Elements of `U_{a', φ, r}` normalize the subgroup generated by `gens`, under the
hypotheses of `commutator_le_closure_gens` for every generator. -/
theorem mem_normalizer_closure_gens (hφ : IsRootDatumValuation i φ)
    {a τ a' : characterLattice S} {t r : ℝ} {P : ℤ → Prop} (ha' : a' ∈ relativeRoots i)
    {w : V S} (haw : eval S a w = 0) (hτw : eval S τ w < 0) (ha'w : eval S a' w ≤ 0)
    (hstep : ∀ (m : ℤ) (n : ℕ), 0 < n → P m → m • a + n • τ ∈ relativeRoots i →
      ∀ p q : ℕ, 0 < p → 0 < q → ∃ (m' : ℤ) (n' : ℕ), 0 < n' ∧ P m' ∧
        p • a' + q • (m • a + n • τ) = m' • a + n' • τ ∧
        (p * r + q * (n * t) : ℝ) = n' * t)
    {c : rationalPoints G} (hc : c ∈ rootFiltration i φ a' r) :
    c ∈ Subgroup.normalizer (Subgroup.closure (gens i φ a τ t P) : Set (rationalPoints G)) := by
  have key : ∀ c' ∈ rootFiltration i φ a' r, ∀ x ∈ gens i φ a τ t P,
      c' * x * c'⁻¹ ∈ Subgroup.closure (gens i φ a τ t P) := by
    intro c' hc' x hx
    obtain ⟨m, n, hn, hm, hd, hx'⟩ := mem_gens.1 hx
    rw [conj_eq_commutator_mul]
    refine mul_mem ?_ (Subgroup.subset_closure hx)
    exact commutator_le_closure_gens hφ ha' haw hτw ha'w hn hd (hstep m n hn hm hd)
      (Subgroup.commutator_mem_commutator (Subgroup.subset_closure hc')
        (Subgroup.subset_closure hx'))
  refine mem_normalizer_closure (key c hc) fun x hx => ?_
  simpa using key c⁻¹ (hφ.inv_mem a' ha' r c hc) x hx

/-- The depth-zero pieces of `U_a` and `U_{-a}` normalize the subgroup generated by all
`U_{m a + n τ, φ, n t}`, `n > 0` (V 3). -/
theorem closure_le_normalizer (hφ : IsRootDatumValuation i φ) {a τ : characterLattice S}
    (t : ℝ) (ha : a ∈ relativeRoots i) (hna : -a ∈ relativeRoots i) {w : V S}
    (haw : eval S a w = 0) (hτw : eval S τ w < 0) :
    Subgroup.closure (rootFiltration i φ a 0 ∪ rootFiltration i φ (-a) 0) ≤
      Subgroup.normalizer
        (Subgroup.closure (gens i φ a τ t fun _ => True) : Set (rationalPoints G)) := by
  rw [Subgroup.closure_le]
  rintro c (hc | hc)
  · refine mem_normalizer_closure_gens hφ ha haw hτw haw.le ?_ hc
    intro m n hn _ _ p q _ hq
    refine ⟨p + q * m, q * n, Nat.mul_pos hq hn, trivial, ?_, ?_⟩
    · module
    · push_cast
      ring
  · refine mem_normalizer_closure_gens hφ hna haw hτw (by rw [eval_neg_char, haw, neg_zero]) ?_ hc
    intro m n hn _ _ p q _ hq
    refine ⟨-p + q * m, q * n, Nat.mul_pos hq hn, trivial, ?_, ?_⟩
    · module
    · push_cast
      ring

/-- The depth bound (internal): an element of `U_τ` in the subgroup generated by all
`U_{m a + n τ, φ, n t}` lies in `U_{τ, φ, t}`. It splits as `y k` with `y ∈ U_{τ, φ, t}` and
`k` in the subgroup generated by the pieces with `m > 0`, and `k = 1` by dynamic separation. -/
theorem le_of_mem_closure_gens (hφ : IsRootDatumValuation i φ) {a τ : characterLattice S}
    {t : ℝ} (hτ : τ ∈ relativeRoots i) {w : V S} (haw : eval S a w = 0)
    (hτw : eval S τ w < 0)
    (hext : ∀ (m : ℤ) (n : ℕ), 0 < n → m • a + n • τ ∈ relativeRoots i →
      (m = 0 ∧ n = 1) ∨ 0 < m)
    {lam : cocharacterLattice S} (hlamτ : latticePairing S τ lam < 0)
    (hlam : ∀ (m : ℤ) (n : ℕ), 0 < m → m • a + n • τ ∈ relativeRoots i →
      0 < latticePairing S (m • a + n • τ) lam)
    {h : rationalPoints G} (hh : h ∈ Subgroup.closure (gens i φ a τ t fun _ => True))
    (hhτ : h ∈ rootGroupPoints i τ) : (t : WithTop ℝ) ≤ φ τ h := by
  let Y : Subgroup (rationalPoints G) :=
    { carrier := rootFiltration i φ τ t
      mul_mem' := fun hx hy => hφ.mul_mem τ hτ t _ _ hx hy
      one_mem' := hφ.one_mem τ hτ t
      inv_mem' := fun hx => hφ.inv_mem τ hτ t _ hx }
  let K := Subgroup.closure (gens i φ a τ t fun m => 0 < m)
  have hYK : Y ≤ Subgroup.normalizer (K : Set (rationalPoints G)) := by
    intro c hc
    refine mem_normalizer_closure_gens hφ hτ haw hτw hτw.le ?_ hc
    intro m n _ hm _ p q hp hq
    refine ⟨q * m, p + q * n, by omega, by positivity, ?_, ?_⟩
    · module
    · push_cast
      ring
  have hle : Subgroup.closure (gens i φ a τ t fun _ => True) ≤ Y ⊔ K := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨m, n, hn, -, hd, hx⟩ := mem_gens.1 hx
    rcases hext m n hn hd with ⟨rfl, rfl⟩ | hm
    · refine Subgroup.mem_sup_left (?_ : x ∈ rootFiltration i φ τ t)
      simpa using hx
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (subset_gens hn hm hd hx))
  have hmem : h ∈ (Y : Set (rationalPoints G)) * (K : Set (rationalPoints G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y K hYK]
    exact hle hh
  obtain ⟨y, hy, k, hk, rfl⟩ := hmem
  have hKU : K ≤ (Dynamic.unipotent (CommGroupScheme.groupHom lam ≫ i)).carrier
      (Over.mk (𝟙 _)) := by
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨m, n, -, hm, hd, hx⟩ := mem_gens.1 hx
    exact RelativeRoot.subgroup_le_dynamicUnipotent i lam (hlam m n hm hd) _ hx.1
  have hkτ : k ∈ rootGroupPoints i τ := by
    have : k = y⁻¹ * (y * k) := by group
    rw [this]
    exact mul_mem (inv_mem hy.1) hhτ
  have hk1 : k = 1 := by
    refine RelativeRoot.eq_one_of_mem_subgroup_of_mem_negative_parabolic i (-lam)
      (by rw [map_neg]; omega) hkτ ?_
    rw [neg_neg]
    exact Dynamic.unipotent_le_parabolic _ _ (hKU hk)
  subst hk1
  simpa using hy.2

/-- The contradiction (internal). Let `n ∈ N(k)` act on characters by the reflection along
`a` with coroot `ν`, lie in the subgroup generated by `U_{a,φ,0}` and `U_{-a,φ,0}`, and move
`φ` by a translation `w` with `a(w) = 0`. Then no root is negative at `w`. -/
theorem not_eval_neg (hS : IsSplitTorus S.toGrp) (hφ : IsRootDatumValuation i φ)
    (hfin : (relativeRoots i).Finite) {a : characterLattice S} (ha : a ∈ relativeRoots i)
    {ν : cocharacterLattice S} (hν : latticePairing S a ν = 2) {n : normalizerPoints i}
    (hn : ∀ χ, weylAction i n⁻¹ χ = χ - latticePairing S χ ν • a)
    (hnc : (n : rationalPoints G) ∈
      Subgroup.closure (rootFiltration i φ a 0 ∪ rootFiltration i φ (-a) 0))
    {w : V S} (hw : n • φ = w +ᵥ φ) (haw : eval S a w = 0) {b : characterLattice S}
    (hb : b ∈ relativeRoots i) (hbw : eval S b w < 0) : False := by
  have hna : -a ∈ relativeRoots i := by
    have := weylAction_mapsTo_relativeRoots i n⁻¹ ha
    rwa [hn, hν, show a - (2 : ℤ) • a = -a by module] at this
  obtain ⟨τ, hτ, hτw, hext⟩ := exists_extremal_root hfin hν haw hb hbw
  obtain ⟨lam, hlamτ, hlam⟩ := exists_separating_cocharacter hS hfin hν haw hτw
  obtain ⟨h₀, hh₀, hh₀top⟩ := hφ.exists_ne_top hτ
  obtain ⟨t₀, ht₀⟩ := WithTop.ne_top_iff_exists.1 hh₀top
  set T := latticePairing S τ ν with hT
  set s := (-T) • a + (1 : ℕ) • τ with hs_def
  have hs : weylAction i n⁻¹ s = τ := by
    rw [hn]
    simp only [hs_def, map_add, map_zsmul, map_nsmul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, hν, ← hT]
    module
  have hns : weylAction i n τ = s := by
    rw [← hs, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      LinearEquiv.coe_one, id]
  set g := (n : rationalPoints G) * h₀ * (n : rationalPoints G)⁻¹ with hg_def
  have hg : g ∈ rootGroupPoints i s := hns ▸ conj_mem_rootGroupPoints n hh₀
  have hval := congrArg (fun ψ : RootFunctionFamily S G => ψ s g) hw
  simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hs, hg_def] at hval
  rw [show (n : rationalPoints G)⁻¹ * ((n : rationalPoints G) * h₀ * (n : rationalPoints G)⁻¹) *
      (n : rationalPoints G) = h₀ by group, ← ht₀] at hval
  have hsw : eval S s w = eval S τ w := by
    rw [hs_def, eval_comb, haw]
    push_cast
    ring
  rw [hsw] at hval
  set t := t₀ - eval S τ w with ht_def
  have hgs : φ s g = (t : WithTop ℝ) := by
    induction h : φ s g using WithTop.recTopCoe with
    | top => rw [h, WithTop.top_add] at hval; exact absurd hval WithTop.coe_ne_top
    | coe r =>
      rw [h, ← WithTop.coe_add, WithTop.coe_inj] at hval
      rw [WithTop.coe_inj, ht_def, hval]
      ring
  have hsΦ : s ∈ relativeRoots i := by
    by_contra hns'
    rw [hφ.eq_top_of_not_mem_roots s hns' g] at hgs
    exact WithTop.top_ne_coe hgs
  have hgH : g ∈ Subgroup.closure (gens i φ a τ t fun _ => True) := by
    refine Subgroup.subset_closure (subset_gens (m := -T) (n := 1) one_pos trivial hsΦ ?_)
    refine ⟨hg, ?_⟩
    rw [hgs, Nat.cast_one, one_mul]
  have hN := inv_mem (closure_le_normalizer hφ t ha hna haw hτw hnc)
  rw [Subgroup.mem_normalizer_iff] at hN
  have hh₀H : h₀ ∈ Subgroup.closure (gens i φ a τ t fun _ => True) := by
    have := (hN g).1 hgH
    rwa [hg_def, show (n : rationalPoints G)⁻¹ * ((n : rationalPoints G) * h₀ *
      (n : rationalPoints G)⁻¹) * (n : rationalPoints G)⁻¹⁻¹ = h₀ by group] at this
  have hle := le_of_mem_closure_gens hφ hτ haw hτw hext hlamτ hlam hh₀H hh₀
  rw [← ht₀, WithTop.coe_le_coe, ht_def] at hle
  linarith

/-- `φ_a(g⁻¹) = φ_a(g)` for a valuation (V 1 and the normalization axioms). -/
theorem apply_inv (hφ : IsRootDatumValuation i φ) (a : characterLattice S)
    (g : rationalPoints G) : φ a g⁻¹ = φ a g := by
  by_cases ha : a ∈ relativeRoots i
  · have key : ∀ h ∈ rootGroupPoints i a, φ a h ≤ φ a h⁻¹ := by
      intro h hh
      induction hv : φ a h using WithTop.recTopCoe with
      | top =>
        have h1 := (hφ.eq_top_iff a ha h hh).1 hv
        subst h1
        rw [inv_one, hv]
      | coe r => exact (hφ.inv_mem a ha r h ⟨hh, hv.ge⟩).2
    by_cases hg : g ∈ rootGroupPoints i a
    · refine le_antisymm ?_ (key g hg)
      simpa using key g⁻¹ (inv_mem hg)
    · rw [hφ.eq_top_of_not_mem a ha g hg,
        hφ.eq_top_of_not_mem a ha g⁻¹ fun h => hg (by simpa using inv_mem h)]
  · rw [hφ.eq_top_of_not_mem_roots a ha, hφ.eq_top_of_not_mem_roots a ha]

end Generators

/-! ### The main argument -/

/-- AS 1 for building data (KP Proposition 6.2.1, fixed-point form). -/
theorem hasRootReflections {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] (B : ValuationBuildingData G) : B.HasRootReflections := by
  intro α u hu h1 p hp x hx
  have := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hfin := hS.finite_relativeRoots B.i
  obtain ⟨a, ha⟩ := α
  have ha0 : a ≠ 0 := ha.1
  set m := B.reflectionElement hp with hm_def
  have hmG : (m : rationalPoints G) = p.1 * u * p.2 := rfl
  have hφ := x.isValuation
  obtain ⟨v, hv⟩ := B.apartment.equipollent_of_mem x.mem (m • x).mem
  rw [KPApartmentData.val_smul] at hv
  obtain ⟨hν, hr⟩ := hp.coroot_spec B.i hS ha0 hu h1
  set ν := hp.coroot B.i hS ha0 hu h1 with hν_def
  have hr' : ∀ χ, weylAction B.i m χ = χ - latticePairing B.S χ ν • a := hr
  have h2 : ∀ χ, weylAction B.i m (weylAction B.i m χ) = χ := by
    intro χ
    rw [hr', hr', map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν,
      smul_eq_mul]
    module
  have hinv : ∀ χ, weylAction B.i m⁻¹ χ = χ - latticePairing B.S χ ν • a := by
    intro χ
    calc weylAction B.i m⁻¹ χ = weylAction B.i m⁻¹ (weylAction B.i m (weylAction B.i m χ)) := by
          rw [h2]
      _ = weylAction B.i m χ := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, LinearEquiv.coe_one,
            id]
      _ = _ := hr' χ
  have hma : weylAction B.i m a = -a := by
    rw [hr', hν, show a - (2 : ℤ) • a = -a by module]
  have hmna : weylAction B.i m⁻¹ (-a) = a := by
    rw [hinv, map_neg, LinearMap.neg_apply, hν, show -a - (-2 : ℤ) • a = a by module]
  have hna : -a ∈ relativeRoots B.i := hma ▸ weylAction_mapsTo_relativeRoots B.i m ha
  -- Depths: `u ∈ U_{a,0}` and `p.1, p.2 ∈ U_{-a,0}` (V 5 for `m` and `m⁻¹`).
  have hu0 : x.val a u = 0 := hx
  have hp1 : x.val (-a) p.1 = 0 := by
    have := hφ.opposite a ha u hu h1 p.1 hp.1 p.2 hp.2.1 hp.2.2
    rwa [hu0, add_zero] at this
  have hminv : p.2⁻¹ * u⁻¹ * p.1⁻¹ ∈ normalizerPoints B.i := by
    have : p.2⁻¹ * u⁻¹ * p.1⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2 : x.val (-a) p.2 = 0 := by
    have := hφ.opposite a ha u⁻¹ (inv_mem hu) (inv_ne_one.2 h1) p.2⁻¹ (inv_mem hp.2.1)
      p.1⁻¹ (inv_mem hp.1) hminv
    rwa [apply_inv hφ, apply_inv hφ, hu0, add_zero] at this
  have hmc : (m : rationalPoints G) ∈
      Subgroup.closure (rootFiltration B.i x.val a 0 ∪ rootFiltration B.i x.val (-a) 0) := by
    rw [hmG]
    refine mul_mem (mul_mem (Subgroup.subset_closure (Or.inr ⟨hp.1, ?_⟩))
      (Subgroup.subset_closure (Or.inl ⟨hu, ?_⟩)))
      (Subgroup.subset_closure (Or.inr ⟨hp.2.1, ?_⟩))
    · rw [hp1, WithTop.coe_zero]
    · rw [hu0, WithTop.coe_zero]
    · rw [hp2, WithTop.coe_zero]
  -- `a(v) = 0`, through `y = m⁻¹ p.1 m ∈ U_a` and `m⁻¹ = y⁻¹ p.2⁻¹ u⁻¹`.
  obtain ⟨y, hy_def⟩ : ∃ y, y = (m : rationalPoints G)⁻¹ * p.1 * m := ⟨_, rfl⟩
  have hy : y ∈ rootGroupPoints B.i a := by
    have := conj_mem_rootGroupPoints m⁻¹ (a := -a) hp.1
    rwa [hmna, InvMemClass.coe_inv, inv_inv, ← hy_def] at this
  have hminv' : y⁻¹ * p.2⁻¹ * u⁻¹ ∈ normalizerPoints B.i := by
    have : y⁻¹ * p.2⁻¹ * u⁻¹ = (m : rationalPoints G)⁻¹ := by
      rw [hy_def, hmG]
      group
    rw [this]
    exact inv_mem m.2
  have hp2ne := (hp.factors_ne_one B.i hS ha0 hu h1).2
  have hy0 : x.val a y = 0 := by
    have := hφ.opposite (-a) hna p.2⁻¹ (inv_mem hp.2.1) (inv_ne_one.2 hp2ne) y⁻¹
      (by rw [neg_neg]; exact inv_mem hy) u⁻¹ (by rw [neg_neg]; exact inv_mem hu) hminv'
    rwa [neg_neg, apply_inv hφ, apply_inv hφ, hp2, add_zero] at this
  have hav : eval B.S a v = 0 := by
    have hval := congrArg (fun ψ : RootFunctionFamily B.S G => ψ (-a) p.1) hv
    simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply, hmna, ← hy_def,
      hy0, hp1, zero_add, eval_neg_char] at hval
    have := (WithTop.coe_eq_zero.1 hval.symm)
    linarith
  -- Every root vanishes at `v`.
  have hall : ∀ d ∈ relativeRoots B.i, eval B.S d v = 0 := by
    intro d hd
    rcases lt_trichotomy (eval B.S d v) 0 with hlt | heq | hgt
    · exact (not_eval_neg hS hφ hfin ha hν hinv hmc hv hav hd hlt).elim
    · exact heq
    · exfalso
      have hv' : m⁻¹ • x.val = (-(m⁻¹ • v)) +ᵥ x.val := by
        have h := congrArg (m⁻¹ • ·) hv
        simp only [inv_smul_smul, RootFunctionFamily.smul_vadd] at h
        calc m⁻¹ • x.val = -(m⁻¹ • v) +ᵥ ((m⁻¹ • v) +ᵥ m⁻¹ • x.val) := by
              rw [neg_vadd_vadd]
          _ = _ := by rw [← h]
      refine not_eval_neg (n := m⁻¹) hS hφ hfin ha hν (fun χ => by rw [inv_inv]; exact hr' χ)
        ?_ hv' ?_ (weylAction_mapsTo_relativeRoots B.i m hd) ?_
      · rw [InvMemClass.coe_inv]
        exact inv_mem hmc
      · rw [map_neg, eval_normalizer_smul, inv_inv, hma, eval_neg_char, hav, neg_zero, neg_zero]
      · rw [map_neg, eval_normalizer_smul, inv_inv, h2]
        linarith
  refine KPApartmentData.Apartment.ext ?_
  rw [KPApartmentData.val_smul, hv]
  exact hφ.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hall)

end RootReflectionProof

/-- KP Proposition 6.2.1 (AS 1): `m(u)` fixes the hyperplane `H_u` pointwise. -/
theorem rootReflection : RootReflectionStatement.{u} := by
  intro F _ _ _ _ G _ B
  exact RootReflectionProof.hasRootReflections B

end Langlands.Geometry.Building
