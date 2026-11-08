import Langlands.Geometry.Building.AffineSimpleRootGram
import Langlands.Group.TitsRestrictedPolysimplicial

/-!
# Every admissible type is the type of a point of the closed chamber

For an affine root system (rank zero allowed), a regular point `c` and an admissible set `X`
of simple reflections of the chamber of `c`, there is a point `x` of the closure of the
chamber fixed by exactly the simple reflections in `X`. The proof is linear algebra: a
Perron–Frobenius argument on isotropic combinations of the simple-root derivatives, and
solvability of a linear system by duality. Consequently the type map is a bijection from the
faces of the chamber onto the admissible sets of simple reflections, reversing the face order.
-/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building.AffineRootSystem

open Langlands.Group.TitsSystem GalleryGeometry

variable {V : Type uV} [AddCommGroup V] [Module ℝ V]

/-! ### Isotropic combinations -/

section Isotropic

variable {ι : Type*} [Fintype ι] (f : ι → Module.Dual ℝ V) (T : Finset V)

/-- `n` is isotropic: the functional `Σ nᵢ fᵢ` vanishes at every vector of `T`. -/
def IsIsotropicCombination (n : ι → ℝ) : Prop :=
  ∀ v ∈ T, ∑ i, n i * f i v = 0

/-- The Gram matrix `G(i,j) = Σ_{v ∈ T} fᵢ(v) fⱼ(v)`. -/
abbrev combinationGram (i j : ι) : ℝ :=
  ∑ v ∈ T, f i v * f j v

variable {f T}

theorem IsIsotropicCombination.sub {n m : ι → ℝ} (hn : IsIsotropicCombination f T n)
    (hm : IsIsotropicCombination f T m) : IsIsotropicCombination f T (n - m) := by
  intro v hv
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hn v hv, hm v hv, sub_zero]

theorem IsIsotropicCombination.smul {n : ι → ℝ} (hn : IsIsotropicCombination f T n) (r : ℝ) :
    IsIsotropicCombination f T (r • n) := by
  intro v hv
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hn v hv, mul_zero]

/-- Expansion of the square norm of a combination in terms of the Gram matrix. -/
theorem sum_sq_combination_eq (m : ι → ℝ) :
    ∑ v ∈ T, (∑ i, m i * f i v) * (∑ j, m j * f j v) =
      ∑ i, ∑ j, m i * m j * combinationGram f T i j := by
  rw [Finset.sum_congr rfl fun v _ => Finset.sum_mul_sum _ _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- With nonpositive off-diagonal Gram entries, isotropic combinations stay isotropic after
taking absolute values. -/
theorem IsIsotropicCombination.abs
    (hG : ∀ i j, i ≠ j → combinationGram f T i j ≤ 0) {n : ι → ℝ}
    (hn : IsIsotropicCombination f T n) : IsIsotropicCombination f T fun i => |n i| := by
  have h0 : ∑ v ∈ T, (∑ i, n i * f i v) * (∑ j, n j * f j v) = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hn v hv, zero_mul]
  have hle : ∑ i, ∑ j, |n i| * |n j| * combinationGram f T i j ≤
      ∑ i, ∑ j, n i * n j * combinationGram f T i j := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      rw [abs_mul_abs_self]
    · have hGij := hG i j hij
      have h2 : n i * n j ≤ |n i| * |n j| := by
        rw [← abs_mul]
        exact le_abs_self _
      nlinarith
  have hsq : ∑ v ∈ T, (∑ i, |n i| * f i v) * (∑ j, |n j| * f j v) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun v _ => mul_self_nonneg _)
    rw [sum_sq_combination_eq]
    rw [sum_sq_combination_eq] at h0
    linarith
  intro v hv
  exact mul_self_eq_zero.1
    ((Finset.sum_eq_zero_iff_of_nonneg (fun v _ => mul_self_nonneg _)).1 hsq v hv)

/-- The Gram matrix annihilates an isotropic combination. -/
theorem IsIsotropicCombination.sum_mul_gram {n : ι → ℝ} (hn : IsIsotropicCombination f T n)
    (i : ι) : ∑ k, n k * combinationGram f T i k = 0 := by
  have : ∑ v ∈ T, f i v * ∑ k, n k * f k v = 0 :=
    Finset.sum_eq_zero fun v hv => by rw [hn v hv, mul_zero]
  calc ∑ k, n k * ∑ v ∈ T, f i v * f k v = ∑ k, ∑ v ∈ T, n k * (f i v * f k v) := by
        simp only [Finset.mul_sum]
    _ = ∑ v ∈ T, ∑ k, n k * (f i v * f k v) := Finset.sum_comm
    _ = ∑ v ∈ T, f i v * ∑ k, n k * f k v := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = 0 := this

/-- Perron–Frobenius step: an isotropic combination vanishing at `i` vanishes at every `j`
with nonzero Gram entry `G(i,j)`. -/
theorem IsIsotropicCombination.eq_zero_of_gram_ne_zero
    (hG : ∀ i j, i ≠ j → combinationGram f T i j ≤ 0) {n : ι → ℝ}
    (hn : IsIsotropicCombination f T n) {i j : ι} (hi : n i = 0)
    (hGij : combinationGram f T i j ≠ 0) : n j = 0 := by
  have hrow := (hn.abs hG).sum_mul_gram i
  have hnonpos : ∀ k ∈ Finset.univ, 0 ≤ -(|n k| * combinationGram f T i k) := by
    intro k _
    by_cases hk : k = i
    · subst hk
      rw [hi, abs_zero, zero_mul, neg_zero]
    · have := hG i k (Ne.symm hk)
      have := abs_nonneg (n k)
      nlinarith
  have hsum : ∑ k, -(|n k| * combinationGram f T i k) = 0 := by
    rw [Finset.sum_neg_distrib, hrow, neg_zero]
  have hj := (Finset.sum_eq_zero_iff_of_nonneg hnonpos).1 hsum j (Finset.mem_univ j)
  rw [neg_eq_zero, mul_eq_zero] at hj
  exact abs_eq_zero.1 (hj.resolve_right hGij)

end Isotropic

/-! ### Solvability of linear systems -/

/-- A system `fᵢ(d) = bᵢ` of finitely many linear equations is solvable as soon as every
linear relation among the `fᵢ` is satisfied by the `bᵢ`. -/
theorem exists_forall_apply_eq_of_relations {ι : Type*} [Fintype ι]
    (f : ι → Module.Dual ℝ V) (b : ι → ℝ)
    (hb : ∀ n : ι → ℝ, (∀ d : V, ∑ i, n i * f i d = 0) → ∑ i, n i * b i = 0) :
    ∃ d : V, ∀ i, f i d = b i := by
  classical
  let F : V →ₗ[ℝ] (ι → ℝ) := LinearMap.pi f
  by_contra hne
  have hnot : b ∉ LinearMap.range F := by
    rintro ⟨d, hd⟩
    exact hne ⟨d, fun i => congrFun hd i⟩
  obtain ⟨φ, hφb, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  let n : ι → ℝ := fun i => φ fun j => if i = j then 1 else 0
  have hφapply : ∀ y : ι → ℝ, φ y = ∑ i, n i * y i := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ φ y]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, mul_comm]
  have hrel : ∀ d : V, ∑ i, n i * f i d = 0 := by
    intro d
    have hmem : φ (F d) ∈ (LinearMap.range F).map φ := ⟨F d, ⟨d, rfl⟩, rfl⟩
    rw [hφ, Submodule.mem_bot] at hmem
    rw [← hmem, hφapply]
    rfl
  exact hφb (by rw [hφapply]; exact hb n hrel)

/-! ### Points of the closed chamber with prescribed type -/

section Chamber

variable {A : Type uA} [AddTorsor V A] {Ψ : Set (A →ᵃ[ℝ] ℝ)}

namespace IsAffineRootSystemWithRankZero

variable (hΨ : IsAffineRootSystemWithRankZero Ψ) {c : A}

include hΨ

/-- Every simple affine root is a positive multiple of the chosen root of a simple
reflection. -/
theorem exists_eq_smul_chamberSimpleRoot {φ : A →ᵃ[ℝ] ℝ}
    (hφ : φ ∈ simpleAffineRoots Ψ (facet Ψ c)) :
    ∃ s : chamberSimpleReflections Ψ (facet Ψ c), ∃ r : ℝ, 0 < r ∧
      φ = r • chamberSimpleRoot s := by
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot φ hφ.1.1
  let s : chamberSimpleReflections Ψ (facet Ψ c) :=
    ⟨⟨affineReflection φ hv.1, affineReflection_mem_affineWeylGroup hφ.1.1 hv⟩,
      ⟨φ, hφ, v, hv, rfl⟩⟩
  have heq := coe_eq_affineReflection_chamberSimpleRoot s
  obtain ⟨r, hr⟩ := exists_eq_smul_of_affineReflection_eq
    (hΨ.linear_ne_zero _ (chamberSimpleRoot_mem s).1.1)
    (isCoroot_chamberSimpleCoroot s).1 hv.1 heq
  refine ⟨s, r, ?_, hr⟩
  have h1 := pos_of_mem_simpleAffineRoots hφ (mem_facet_self Ψ c)
  have h2 := pos_of_mem_simpleAffineRoots (chamberSimpleRoot_mem s) (mem_facet_self Ψ c)
  rw [hr, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at h1
  exact lt_of_not_ge fun h => by nlinarith

/-- For every admissible set `X` of simple reflections of the chamber of `c` there is a point
of the closed chamber fixed by exactly the simple reflections in `X`. -/
theorem exists_mem_facetClosure_fixingSimpleReflections_eq (hc : IsRegular Ψ c)
    {X : Set (affineWeylGroup Ψ)}
    (hX : IsAdmissibleType (chamberSimpleReflections Ψ (facet Ψ c)) X) :
    ∃ x ∈ facetClosure Ψ c, fixingSimpleReflections Ψ (facet Ψ c) x = X := by
  classical
  set S := chamberSimpleReflections Ψ (facet Ψ c) with hS_def
  have : Fintype S := (finite_chamberSimpleReflections hΨ hc).fintype
  set T := hΨ.finite_corootSet.toFinset with hT_def
  let f : S → Module.Dual ℝ V := fun s => (chamberSimpleRoot s).linear
  have hG : ∀ s t : S, s ≠ t → combinationGram f T s t ≤ 0 :=
    fun s t hst => hΨ.chamberSimpleGram_nonpos hc hst
  have hGne : ∀ s t : S, (s : affineWeylGroup Ψ) * t ≠ t * s →
      combinationGram f T s t ≠ 0 :=
    fun s t h => hΨ.chamberSimpleGram_ne_zero h
  -- zero propagation along components
  have hprop : ∀ {n : S → ℝ}, IsIsotropicCombination f T n → ∀ {s : S}, n s = 0 →
      ∀ {t : affineWeylGroup Ψ}, SameComponent S s t → ∀ ht : t ∈ S, n ⟨t, ht⟩ = 0 := by
    intro n hn s hs t hst
    induction hst with
    | refl => intro _; exact hs
    | tail _ hbc ih =>
      intro ht
      exact hn.eq_zero_of_gram_ne_zero hG (ih hbc.1) (hGne ⟨_, hbc.1⟩ ⟨_, ht⟩ hbc.2.2)
  -- positivity along components
  have hpos : ∀ {n : S → ℝ}, IsIsotropicCombination f T n → ∀ {s : S}, 0 < n s →
      ∀ {t : affineWeylGroup Ψ}, SameComponent S s t → ∀ ht : t ∈ S, 0 < n ⟨t, ht⟩ := by
    intro n hn s hs t hst ht
    have hm : IsIsotropicCombination f T ((fun i => |n i|) - n) := (hn.abs hG).sub hn
    have hm0 := hprop hm (s := s) (by simp [abs_of_pos hs]) hst ht
    simp only [Pi.sub_apply, sub_eq_zero] at hm0
    refine lt_of_le_of_ne (hm0 ▸ abs_nonneg _) fun h0 => ?_
    have := hprop hn (s := ⟨t, ht⟩) h0.symm (sameComponent_symm hst) s.2
    exact hs.ne' this
  -- proportionality along components
  have hratio : ∀ {n p : S → ℝ}, IsIsotropicCombination f T n →
      IsIsotropicCombination f T p → ∀ {t : S}, p t ≠ 0 → ∀ {s : affineWeylGroup Ψ},
      SameComponent S t s → ∀ hs : s ∈ S, n ⟨s, hs⟩ = n t / p t * p ⟨s, hs⟩ := by
    intro n p hn hp t hpt s hts hs
    have hm := hn.sub (hp.smul (n t / p t))
    have hm0 := hprop hm (s := t) (by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring) hts hs
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero] at hm0
    exact hm0
  -- chosen nonnegative isotropic vectors
  let P : S → S → ℝ := fun t =>
    if h : ∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0 then fun s => |h.choose s| else 0
  have hPiso : ∀ t, IsIsotropicCombination f T (P t) := by
    intro t
    by_cases h : ∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0
    · simp only [P, h, ↓reduceDIte]
      exact h.choose_spec.1.abs hG
    · simp only [P, h, ↓reduceDIte]
      intro v _
      simp
  have hPnn : ∀ t s, 0 ≤ P t s := by
    intro t s
    by_cases h : ∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0
    · simp only [P, h, ↓reduceDIte]
      exact abs_nonneg _
    · simp [P, h]
  have hPt : ∀ t, (∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0) → 0 < P t t := by
    intro t h
    simp only [P, h, ↓reduceDIte]
    exact abs_pos.2 h.choose_spec.2
  have hPs : ∀ t, (∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0) →
      ∀ s : S, SameComponent S t s → 0 < P t s :=
    fun t h s hts => hpos (hPiso t) (hPt t h) hts s.2
  -- the part of the component of `t` outside `X`
  let F : S → Finset S := fun t =>
    Finset.univ.filter fun s => (s : affineWeylGroup Ψ) ∉ X ∧ SameComponent S t s
  have hFne : ∀ t : S, (F t).Nonempty := by
    intro t
    obtain ⟨u, hu, htu, huX⟩ := hX.2 t t.2
    exact ⟨⟨u, hu⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, huX, htu⟩⟩
  let ψc : S → ℝ := fun s => chamberSimpleRoot s c
  have hψc : ∀ s, 0 < ψc s := fun s =>
    pos_of_mem_simpleAffineRoots (chamberSimpleRoot_mem s) (mem_facet_self Ψ c)
  let w : S → S → ℝ := fun t s =>
    if s = t then -ψc t else if s ∈ F t then ψc t * P t t / (P t s * (F t).card) else 0
  let XS : Finset S := Finset.univ.filter fun t => (t : affineWeylGroup Ψ) ∈ X
  let b : S → ℝ := fun s => ψc s + ∑ t ∈ XS, w t s
  have hbX : ∀ s : S, (s : affineWeylGroup Ψ) ∈ X → b s = 0 := by
    intro s hsX
    have hsum : ∑ t ∈ XS, w t s = w s s := by
      refine Finset.sum_eq_single s (fun t _ hts => ?_) fun hs => absurd
        (show s ∈ XS from Finset.mem_filter.2 ⟨Finset.mem_univ s, hsX⟩) hs
      have hsF : s ∉ F t := fun h => (Finset.mem_filter.1 h).2.1 hsX
      have hst : s ≠ t := Ne.symm hts
      simp only [w, hst, hsF, ↓reduceIte]
    simp [b, hsum, w]
  have hbpos : ∀ s : S, (s : affineWeylGroup Ψ) ∉ X → 0 < b s := by
    intro s hsX
    have hnn : 0 ≤ ∑ t ∈ XS, w t s := by
      refine Finset.sum_nonneg fun t ht => ?_
      have htX := (Finset.mem_filter.1 ht).2
      have hst : s ≠ t := fun h => hsX (h ▸ htX)
      simp only [w, hst, ↓reduceIte]
      split_ifs
      · exact div_nonneg (mul_nonneg (hψc t).le (hPnn t t))
          (mul_nonneg (hPnn t s) (Nat.cast_nonneg _))
      · exact le_rfl
    have := hψc s
    simp only [b]
    linarith
  -- every linear relation is satisfied by `b - ψ(c)`
  have hrel : ∀ n : S → ℝ, (∀ d : V, ∑ s, n s * f s d = 0) →
      ∑ s, n s * (b s - ψc s) = 0 := by
    intro n hn
    have hiso : IsIsotropicCombination f T n := fun v _ => hn v
    have hb' : ∀ s, b s - ψc s = ∑ t ∈ XS, w t s := fun s => by simp only [b]; ring
    simp_rw [hb', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t ht => ?_
    have htX := (Finset.mem_filter.1 ht).2
    have htF : t ∉ F t := fun h => (Finset.mem_filter.1 h).2.1 htX
    have hsplit : ∀ s, n s * w t s = (if s = t then n s * -ψc t else 0) +
        (if s ∈ F t then n s * (ψc t * P t t / (P t s * (F t).card)) else 0) := by
      intro s
      by_cases hst : s = t
      · subst hst
        simp [w, htF]
      · simp only [w, hst, ↓reduceIte, zero_add]
        split_ifs <;> simp
    rw [Finset.sum_congr rfl fun s _ => hsplit s, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_mem, Finset.univ_inter]
    simp only [Finset.mem_univ, ↓reduceIte]
    by_cases h : ∃ p, IsIsotropicCombination f T p ∧ p t ≠ 0
    · have hPt' := hPt t h
      have hcard : ((F t).card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hFne t).card_pos.ne'
      have hterm : ∀ s ∈ F t, n s * (ψc t * P t t / (P t s * (F t).card)) =
          n t * ψc t / (F t).card := by
        intro s hs
        have hsc := (Finset.mem_filter.1 hs).2.2
        have hPs' := hPs t h s hsc
        have hns := hratio hiso (hPiso t) hPt'.ne' hsc s.2
        change n s = n t / P t t * P t s at hns
        rw [hns]
        field_simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      field_simp
      ring
    · have hnt : n t = 0 := by
        by_contra hne
        exact h ⟨n, hiso, hne⟩
      have hP0 : P t = 0 := by
        simp only [P, h, ↓reduceDIte]
      simp [hnt, hP0]
  obtain ⟨d, hd⟩ := exists_forall_apply_eq_of_relations f (fun s => b s - ψc s) hrel
  have hx : ∀ s : S, chamberSimpleRoot s (d +ᵥ c) = b s := by
    intro s
    have := hd s
    simp only [f] at this
    rw [AffineMap.map_vadd, this, vadd_eq_add]
    simp only [ψc]
    ring
  have hb_nonneg : ∀ s : S, 0 ≤ b s := by
    intro s
    by_cases hsX : (s : affineWeylGroup Ψ) ∈ X
    · exact (hbX s hsX).ge
    · exact (hbpos s hsX).le
  refine ⟨d +ᵥ c, ?_, ?_⟩
  · refine (mem_facetClosure_iff_simple_nonneg hΨ hc _).2 fun φ hφ => ?_
    obtain ⟨s, r, hr, rfl⟩ := hΨ.exists_eq_smul_chamberSimpleRoot hφ
    rw [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, hx s]
    exact mul_nonneg hr.le (hb_nonneg s)
  · ext s
    constructor
    · rintro ⟨hs, hfix⟩
      by_contra hsX
      have h0 := (apply_eq_self_iff_chamberSimpleRoot ⟨s, hs⟩ (d +ᵥ c)).1 hfix
      rw [hx] at h0
      exact (hbpos ⟨s, hs⟩ hsX).ne' h0
    · intro hsX
      have hs := hX.1 hsX
      refine ⟨hs, (apply_eq_self_iff_chamberSimpleRoot ⟨s, hs⟩ (d +ᵥ c)).2 ?_⟩
      rw [hx]
      exact hbX ⟨s, hs⟩ hsX

/-- If every simple root vanishing at `x` vanishes at `y` (both in the closed chamber), every
root vanishing at `x` vanishes at `y`. -/
theorem apply_eq_zero_of_simple_zero_imp (hc : IsRegular Ψ c) {x y : A}
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c)
    (hxy : ∀ ψ ∈ simpleAffineRoots Ψ (facet Ψ c), ψ x = 0 → ψ y = 0)
    {η : A →ᵃ[ℝ] ℝ} (hη : η ∈ Ψ) (hηx : η x = 0) : η y = 0 := by
  by_contra hηy
  obtain ⟨t, ht, hsign⟩ := exists_pos_of_eventually
    (eventually_sign_smul_vadd hΨ.isLocallyFiniteReflectionArrangement x (x -ᵥ y))
  have happ : ∀ ζ : A →ᵃ[ℝ] ℝ, ζ (t • (x -ᵥ y) +ᵥ x) = ζ x + t * (ζ x - ζ y) := by
    intro ζ
    rw [GalleryGeometry.apply_smul_vadd, AffineMap.linearMap_vsub, vsub_eq_sub]
  have hz : t • (x -ᵥ y) +ᵥ x ∈ facetClosure Ψ c := by
    refine (mem_facetClosure_iff_simple_nonneg hΨ hc _).2 fun ψ hψ => ?_
    by_cases hψx : ψ x = 0
    · rw [happ, hψx, hxy ψ hψ hψx]
      simp
    · have hpos : 0 < ψ x :=
        lt_of_le_of_ne ((mem_facetClosure_iff_simple_nonneg hΨ hc x).1 hx ψ hψ) (Ne.symm hψx)
      have h := hsign ψ hψ.1.1 hψx
      rw [sign_pos hpos, sign_eq_one_iff] at h
      exact h.le
  have hηz : η (t • (x -ᵥ y) +ᵥ x) = -(t * η y) := by
    rw [happ, hηx]
    ring
  have hyc : SignType.sign (η y) = SignType.sign (η c) :=
    (hy η hη).resolve_left (by rwa [sign_eq_zero_iff])
  rcases hz η hη with h | h
  · rw [sign_eq_zero_iff, hηz, neg_eq_zero] at h
    exact hηy ((mul_eq_zero.mp h).resolve_left ht.ne')
  · rw [← hyc, hηz] at h
    rcases lt_or_gt_of_ne hηy with hlt | hlt
    · have hneg : 0 < -(t * η y) := by nlinarith
      rw [sign_pos hneg, sign_neg hlt] at h
      exact absurd h (by decide)
    · have hneg : -(t * η y) < 0 := by nlinarith
      rw [sign_neg hneg, sign_pos hlt] at h
      exact absurd h (by decide)

/-- Simple roots vanishing at a point correspond to simple reflections fixing it. -/
theorem simple_zero_imp_of_fixingSimpleReflections_subset {x y : A}
    (h : fixingSimpleReflections Ψ (facet Ψ c) x ⊆ fixingSimpleReflections Ψ (facet Ψ c) y) :
    ∀ φ ∈ simpleAffineRoots Ψ (facet Ψ c), φ x = 0 → φ y = 0 := by
  intro φ hφ hφx
  obtain ⟨s, r, hr, rfl⟩ := hΨ.exists_eq_smul_chamberSimpleRoot hφ
  simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_eq_zero, hr.ne',
    false_or] at hφx ⊢
  have hsx : (s : affineWeylGroup Ψ) ∈ fixingSimpleReflections Ψ (facet Ψ c) x :=
    ⟨s.2, (apply_eq_self_iff_chamberSimpleRoot s x).2 hφx⟩
  exact (apply_eq_self_iff_chamberSimpleRoot s y).1 (h hsx).2

/-- In the closed chamber, `x` lies in the closure of the facet of `y` exactly when every simple
reflection fixing `y` fixes `x`. -/
theorem mem_facetClosure_iff_fixingSimpleReflections_subset (hc : IsRegular Ψ c) {x y : A}
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c) :
    x ∈ facetClosure Ψ y ↔
      fixingSimpleReflections Ψ (facet Ψ c) y ⊆ fixingSimpleReflections Ψ (facet Ψ c) x := by
  constructor
  · rintro hxy s ⟨hs, hfix⟩
    refine ⟨hs, ?_⟩
    have h0 := (apply_eq_self_iff_chamberSimpleRoot ⟨s, hs⟩ y).1 hfix
    refine (apply_eq_self_iff_chamberSimpleRoot ⟨s, hs⟩ x).2 ?_
    rcases hxy _ (chamberSimpleRoot_mem ⟨s, hs⟩).1.1 with h | h
    · exact sign_eq_zero_iff.1 h
    · rw [h0, sign_zero] at h
      exact sign_eq_zero_iff.1 h
  · intro hsub η hη
    by_cases hηy : η y = 0
    · left
      rw [hΨ.apply_eq_zero_of_simple_zero_imp hc hy hx
        (hΨ.simple_zero_imp_of_fixingSimpleReflections_subset hsub) hη hηy, sign_zero]
    · by_cases hηx : η x = 0
      · left
        rw [hηx, sign_zero]
      · right
        rw [(hx η hη).resolve_left (by rwa [sign_eq_zero_iff]),
          (hy η hη).resolve_left (by rwa [sign_eq_zero_iff])]

/-- Points of the closed chamber with the same fixing simple reflections lie in the same
facet. -/
theorem facetRel_of_fixingSimpleReflections_eq (hc : IsRegular Ψ c) {x y : A}
    (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c)
    (h : fixingSimpleReflections Ψ (facet Ψ c) x = fixingSimpleReflections Ψ (facet Ψ c) y) :
    facetRel Ψ x y := by
  rw [facetRel_iff_simple_zero_iff hΨ hc hx hy]
  intro ψ hψ
  exact ⟨hΨ.simple_zero_imp_of_fixingSimpleReflections_subset h.le ψ hψ,
    hΨ.simple_zero_imp_of_fixingSimpleReflections_subset h.ge ψ hψ⟩

omit hΨ in
/-- A face of the chamber of `c` is the facet of a point of its closure. -/
theorem exists_eq_facet_of_isFaceOf {Fa : Set A} (hFa : IsFaceOf Ψ Fa (facet Ψ c)) :
    ∃ x ∈ facetClosure Ψ c, Fa = facet Ψ x := by
  obtain ⟨⟨x, rfl⟩, y, hy, hsub⟩ := hFa
  refine ⟨x, ?_, rfl⟩
  rw [← facetClosure_eq_of_facetRel (facet_eq_facet_iff.1 hy)]
  exact hsub (mem_facet_self Ψ x)

omit hΨ in
/-- The facet of a point of the closed chamber is a face of the chamber. -/
theorem isFaceOf_facet_of_mem_facetClosure {x : A} (hx : x ∈ facetClosure Ψ c) :
    IsFaceOf Ψ (facet Ψ x) (facet Ψ c) :=
  ⟨⟨x, rfl⟩, c, rfl, facet_subset_facetClosure_iff.2 hx⟩

/-- Every admissible set of simple reflections is the type of a face of the chamber. -/
theorem exists_isFaceOf_facetSimpleReflections_eq (hc : IsRegular Ψ c)
    {X : Set (affineWeylGroup Ψ)}
    (hX : IsAdmissibleType (chamberSimpleReflections Ψ (facet Ψ c)) X) :
    ∃ Fa, IsFaceOf Ψ Fa (facet Ψ c) ∧ facetSimpleReflections Ψ (facet Ψ c) Fa = X := by
  obtain ⟨x, hx, hxX⟩ := hΨ.exists_mem_facetClosure_fixingSimpleReflections_eq hc hX
  exact ⟨facet Ψ x, isFaceOf_facet_of_mem_facetClosure hx,
    (facetSimpleReflections_facet_eq _ x).trans hxX⟩

/-- The type map is a bijection from the faces of the chamber of `c` onto the admissible sets
of its simple reflections. -/
theorem bijOn_facetSimpleReflections (hc : IsRegular Ψ c) :
    Set.BijOn (facetSimpleReflections Ψ (facet Ψ c)) {Fa | IsFaceOf Ψ Fa (facet Ψ c)}
      {X | IsAdmissibleType (chamberSimpleReflections Ψ (facet Ψ c)) X} := by
  refine ⟨fun Fa hFa => hΨ.isAdmissibleType_facetSimpleReflections ⟨c, hc, rfl⟩ hFa.1,
    fun Fa hFa Fb hFb hab => ?_, fun X hX => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := exists_eq_facet_of_isFaceOf hFa
    obtain ⟨y, hy, rfl⟩ := exists_eq_facet_of_isFaceOf hFb
    rw [facetSimpleReflections_facet_eq, facetSimpleReflections_facet_eq] at hab
    exact facet_eq_facet_iff.2 (hΨ.facetRel_of_fixingSimpleReflections_eq hc hx hy hab)
  · obtain ⟨Fa, hFa, hX'⟩ := hΨ.exists_isFaceOf_facetSimpleReflections_eq hc hX
    exact ⟨Fa, hFa, hX'⟩

/-- For faces of the chamber of `c`, one lies in the closure of the other exactly when the
types are in the reverse inclusion. -/
theorem subset_facetClosure_iff_facetSimpleReflections_subset (hc : IsRegular Ψ c)
    {x y : A} (hx : x ∈ facetClosure Ψ c) (hy : y ∈ facetClosure Ψ c) :
    facet Ψ x ⊆ facetClosure Ψ y ↔
      facetSimpleReflections Ψ (facet Ψ c) (facet Ψ y) ⊆
        facetSimpleReflections Ψ (facet Ψ c) (facet Ψ x) := by
  rw [facet_subset_facetClosure_iff, facetSimpleReflections_facet_eq,
    facetSimpleReflections_facet_eq]
  exact hΨ.mem_facetClosure_iff_fixingSimpleReflections_subset hc hx hy

end IsAffineRootSystemWithRankZero

end Chamber

end Langlands.Geometry.Building.AffineRootSystem
