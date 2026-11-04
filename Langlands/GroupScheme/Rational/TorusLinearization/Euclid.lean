import Langlands.GroupScheme.Rational.TorusLinearization.AdditivePolynomials

/-! # Euclidean division of additive polynomials and Frobenius bases -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

section FrobeniusSpan

variable {n : ℕ} (A : Type u) [CommRing A] (p : ℕ)

/-- The span of the one-variable monomials `X ^ p ^ r` with `r ≥ m`. -/
def frobSpan₁ (m : ℕ) : Submodule A (Polynomial A) :=
  Submodule.span A {φ | ∃ r, m ≤ r ∧ φ = Polynomial.X ^ p ^ r}

/-- The Frobenius span of `S` from level `m`: the span of the `g ^ p ^ r`, `g ∈ S`, `r ≥ m`. -/
def frobSpan (m : ℕ) (S : Set (MvPolynomial (Fin n) A)) : Submodule A (MvPolynomial (Fin n) A) :=
  Submodule.span A {f | ∃ g ∈ S, ∃ r, m ≤ r ∧ f = g ^ p ^ r}

variable {A p}

theorem frobSpan_mono {m : ℕ} {S S' : Set (MvPolynomial (Fin n) A)} (h : S ⊆ S') :
    frobSpan A p m S ≤ frobSpan A p m S' := by
  apply Submodule.span_mono
  rintro _ ⟨g, hg, r, hr, rfl⟩
  exact ⟨g, h hg, r, hr, rfl⟩

theorem pow_mem_frobSpan {m r : ℕ} {S : Set (MvPolynomial (Fin n) A)} {g : MvPolynomial (Fin n) A}
    (hg : g ∈ S) (hr : m ≤ r) : g ^ p ^ r ∈ frobSpan A p m S :=
  Submodule.subset_span ⟨g, hg, r, hr, rfl⟩

theorem aeval_mem_frobSpan {m : ℕ} {S : Set (MvPolynomial (Fin n) A)}
    {g : MvPolynomial (Fin n) A} (hg : g ∈ S) {ψ : Polynomial A} (hψ : ψ ∈ frobSpan₁ A p m) :
    Polynomial.aeval g ψ ∈ frobSpan A p m S := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [map_pow, Polynomial.aeval_X]
    exact pow_mem_frobSpan hg hr
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem frobSpan₁_le_addPolys₁ [Fact p.Prime] (h0 : (p : A) = 0) (m : ℕ) :
    frobSpan₁ A p m ≤ addPolys₁ A := by
  rw [frobSpan₁, Submodule.span_le]
  rintro _ ⟨r, -, rfl⟩
  exact isAddPoly₁_X.pow_char p h0 r

theorem coeff_one_eq_zero_of_mem_frobSpan₁ [Fact p.Prime] {ψ : Polynomial A}
    (hψ : ψ ∈ frobSpan₁ A p 1) : ψ.coeff 1 = 0 := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    rw [Polynomial.coeff_X_pow]
    have : 1 < p ^ r := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
    simp [show (1 : ℕ) ≠ p ^ r by omega]
  | zero => simp
  | add x y _ _ hx hy => rw [Polynomial.coeff_add, hx, hy, add_zero]
  | smul c x _ hx => rw [Polynomial.coeff_smul, hx, smul_zero]

/-- Elements of a Frobenius span of a finite set are sums of additive substitutions. -/
theorem exists_eq_sum_of_mem_frobSpan {m : ℕ} {G : Finset (MvPolynomial (Fin n) A)}
    {x : MvPolynomial (Fin n) A} (hx : x ∈ frobSpan A p m (G : Set (MvPolynomial (Fin n) A))) :
    ∃ ψ : MvPolynomial (Fin n) A → Polynomial A, (∀ g, ψ g ∈ frobSpan₁ A p m) ∧
      x = ∑ g ∈ G, Polynomial.aeval g (ψ g) := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, r, hr, rfl⟩ := hx
    refine ⟨Pi.single g (Polynomial.X ^ p ^ r), fun g' => ?_, ?_⟩
    · by_cases h : g' = g
      · subst h
        rw [Pi.single_eq_same]
        exact Submodule.subset_span ⟨r, hr, rfl⟩
      · rw [Pi.single_eq_of_ne h]
        exact zero_mem _
    · rw [Finset.sum_eq_single_of_mem g hg, Pi.single_eq_same, map_pow, Polynomial.aeval_X]
      intro g' _ hg'
      rw [Pi.single_eq_of_ne hg', map_zero]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨ψ, hψ, rfl⟩ := hx
    obtain ⟨ψ', hψ', rfl⟩ := hy
    refine ⟨ψ + ψ', fun g => add_mem (hψ g) (hψ' g), ?_⟩
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  | smul c x _ hx =>
    obtain ⟨ψ, hψ, rfl⟩ := hx
    refine ⟨c • ψ, fun g => Submodule.smul_mem _ c (hψ g), ?_⟩
    simp only [Pi.smul_apply, map_smul, Finset.smul_sum]

end FrobeniusSpan

section Division

variable {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

theorem IsAddPoly₁.mem_frobSpan₁ {φ : Polynomial k} (hφ : IsAddPoly₁ φ) :
    φ ∈ frobSpan₁ k p 0 := by
  rw [φ.as_sum_support_C_mul_X_pow]
  refine Submodule.sum_mem _ fun d hd => ?_
  have : ∃ r, d = p ^ r := by
    by_contra h
    push Not at h
    exact Polynomial.mem_support_iff.mp hd (hφ.coeff_eq_zero k p h)
  obtain ⟨r, rfl⟩ := this
  rw [← Polynomial.smul_eq_C_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, Nat.zero_le r, rfl⟩)

theorem IsAddPoly₁.natDegree_eq_pow {φ : Polynomial k} (hφ : IsAddPoly₁ φ) (h0 : φ ≠ 0) :
    ∃ m, φ.natDegree = p ^ m := by
  by_contra h
  push Not at h
  exact h0 (Polynomial.leadingCoeff_eq_zero.mp (hφ.coeff_eq_zero k p h))

include hp in
theorem IsAddPoly₁.one_le_natDegree {φ : Polynomial k} (hφ : IsAddPoly₁ φ) (h0 : φ ≠ 0) :
    1 ≤ φ.natDegree := by
  obtain ⟨m, hm⟩ := hφ.natDegree_eq_pow (p := p) h0
  rw [hm]
  exact Nat.one_le_pow _ _ hp.out.pos

include hp in
theorem IsAddPoly₁.comp_ne_zero {ψ h : Polynomial k} (hψ : IsAddPoly₁ ψ) (hh : IsAddPoly₁ h)
    (hψ0 : ψ ≠ 0) (hh0 : h ≠ 0) : ψ.comp h ≠ 0 := by
  intro hc
  have hdeg := congrArg Polynomial.natDegree hc
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_zero] at hdeg
  have h1 := hψ.one_le_natDegree (p := p) hψ0
  have h2 := hh.one_le_natDegree (p := p) hh0
  exact mul_ne_zero (Nat.one_le_iff_ne_zero.mp h1) (Nat.one_le_iff_ne_zero.mp h2) hdeg

theorem degree_zero_lt {h : Polynomial k} (hh0 : h ≠ 0) : (0 : Polynomial k).degree < h.degree := by
  rw [Polynomial.degree_zero]
  exact bot_lt_iff_ne_bot.mpr (Polynomial.degree_ne_bot.mpr hh0)

include hp in
/-- Euclidean division of additive polynomials with respect to composition. -/
theorem IsAddPoly₁.exists_comp_add {h : Polynomial k} (hh : IsAddPoly₁ h) (hh0 : h ≠ 0) :
    ∀ φ : Polynomial k, IsAddPoly₁ φ → ∃ ψ ρ : Polynomial k, IsAddPoly₁ ψ ∧ IsAddPoly₁ ρ ∧
      φ = ψ.comp h + ρ ∧ ρ.degree < h.degree := by
  intro φ hφ
  induction hd : φ.natDegree using Nat.strong_induction_on generalizing φ with
  | _ d ih =>
  by_cases hlt : φ.degree < h.degree
  · exact ⟨0, φ, isAddPoly₁_zero, hφ, by simp, hlt⟩
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact hlt (degree_zero_lt hh0)
  obtain ⟨m, hm⟩ := hφ.natDegree_eq_pow (p := p) hφ0
  obtain ⟨e, he⟩ := hh.natDegree_eq_pow (p := p) hh0
  have hle : h.natDegree ≤ φ.natDegree :=
    Polynomial.natDegree_le_natDegree (not_lt.mp hlt)
  have hem : e ≤ m := by
    rw [hm, he] at hle
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp hle
  have hlc0 : h.leadingCoeff ^ p ^ (m - e) ≠ 0 :=
    pow_ne_zero _ (Polynomial.leadingCoeff_ne_zero.mpr hh0)
  set c := φ.leadingCoeff / h.leadingCoeff ^ p ^ (m - e) with hc
  have hc0 : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hφ0) hlc0
  set ψ₀ : Polynomial k := Polynomial.C c * Polynomial.X ^ p ^ (m - e) with hψ₀def
  have hψ₀ : IsAddPoly₁ ψ₀ := by
    rw [hψ₀def, ← Polynomial.smul_eq_C_mul]
    exact (isAddPoly₁_X.pow_char p (CharP.cast_eq_zero k p) _).smul c
  have hcomp : ψ₀.comp h = Polynomial.C c * h ^ p ^ (m - e) := by
    simp [hψ₀def]
  have hne : ψ₀.comp h ≠ 0 := by
    rw [hcomp]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero _ hh0)
  have hnat : (ψ₀.comp h).natDegree = φ.natDegree := by
    rw [hcomp, Polynomial.natDegree_C_mul hc0, Polynomial.natDegree_pow, he, hm, ← pow_add,
      Nat.sub_add_cancel hem]
  have hdeg : φ.degree = (ψ₀.comp h).degree := by
    rw [Polynomial.degree_eq_natDegree hφ0, Polynomial.degree_eq_natDegree hne, hnat]
  have hlc : φ.leadingCoeff = (ψ₀.comp h).leadingCoeff := by
    rw [hcomp, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_pow, hc, div_mul_cancel₀ _ hlc0]
  have hφ' : IsAddPoly₁ (φ - ψ₀.comp h) := hφ.sub (hψ₀.comp hh)
  have hlt' : (φ - ψ₀.comp h).degree < φ.degree :=
    Polynomial.degree_sub_lt_left hdeg hφ0 hlc
  by_cases h0' : φ - ψ₀.comp h = 0
  · refine ⟨ψ₀, 0, hψ₀, isAddPoly₁_zero, ?_, degree_zero_lt hh0⟩
    rw [add_zero, ← sub_eq_zero]
    exact h0'
  obtain ⟨ψ', ρ, hψ', hρ, heq, hρd⟩ :=
    ih _ (hd ▸ Polynomial.natDegree_lt_natDegree h0' hlt') _ hφ' rfl
  refine ⟨ψ₀ + ψ', ρ, hψ₀.add hψ', hρ, ?_, hρd⟩
  rw [Polynomial.add_comp, add_assoc, ← heq]
  ring

end Division

section FrobeniusBasis

variable {n : ℕ} {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

/-- Frobenius independence of a finite family of polynomials: no nontrivial relation
`∑ g, ψ_g(g) = 0` with additive one-variable polynomials `ψ_g`. -/
def FrobIndep (G : Finset (MvPolynomial (Fin n) k)) : Prop :=
  ∀ ψ : MvPolynomial (Fin n) k → Polynomial k, (∀ g ∈ G, IsAddPoly₁ (ψ g)) →
    ∑ g ∈ G, Polynomial.aeval g (ψ g) = 0 → ∀ g ∈ G, ψ g = 0

omit hp [CharP k p] in
theorem part_aeval (j : Fin n) (g : MvPolynomial (Fin n) k) (φ : Polynomial k) :
    part j (Polynomial.aeval g φ) = φ.comp (part j g) := by
  rw [← Polynomial.aeval_algHom_apply, Polynomial.comp_eq_aeval]

omit hp [CharP k p] in
theorem IsAddPoly₁.comp_zero {φ : Polynomial k} (hφ : IsAddPoly₁ φ) : φ.comp 0 = 0 := by
  rw [Polynomial.comp_zero, ← Polynomial.coeff_zero_eq_eval_zero, hφ.coeff_zero, map_zero]

omit hp [CharP k p] in
theorem pow_pow_mem_of_frobClosed {N : Submodule k (MvPolynomial (Fin n) k)}
    (hN : ∀ f ∈ N, f ^ p ∈ N) {g : MvPolynomial (Fin n) k} (hg : g ∈ N) (r : ℕ) :
    g ^ p ^ r ∈ N := by
  induction r with
  | zero => simpa using hg
  | succ r ih =>
    rw [pow_succ p r, pow_mul]
    exact hN _ ih

omit hp [CharP k p] in
theorem aeval_mem_of_frobClosed {N : Submodule k (MvPolynomial (Fin n) k)}
    (hN : ∀ f ∈ N, f ^ p ∈ N) {g : MvPolynomial (Fin n) k} (hg : g ∈ N) {ψ : Polynomial k}
    (hψ : ψ ∈ frobSpan₁ k p 0) : Polynomial.aeval g ψ ∈ N := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, -, rfl⟩ := hx
    rw [map_pow, Polynomial.aeval_X]
    exact pow_pow_mem_of_frobClosed hN hg r
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

/-- The Frobenius raises the level of a Frobenius span. -/
theorem pow_mem_frobSpan_succ {m : ℕ} {S : Set (MvPolynomial (Fin n) k)}
    {x : MvPolynomial (Fin n) k} (hx : x ∈ frobSpan k p m S) : x ^ p ∈ frobSpan k p (m + 1) S := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, r, hr, rfl⟩ := hx
    rw [← pow_mul, ← pow_succ]
    exact pow_mem_frobSpan hg (by omega)
  | zero => rw [zero_pow hp.out.ne_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_pow_char]; exact add_mem hx hy
  | smul c x _ hx => rw [smul_pow]; exact Submodule.smul_mem _ _ hx

/-- A Frobenius-closed space of additive polynomials supported on the variables in `s` has a
finite Frobenius-independent generating family (left Euclidean algorithm). -/
theorem exists_frobBasis (s : Finset (Fin n)) :
    ∀ N : Submodule k (MvPolynomial (Fin n) k), (∀ f ∈ N, IsAddPoly f) →
      (∀ f ∈ N, f ^ p ∈ N) → (∀ f ∈ N, ∀ j ∉ s, part j f = 0) →
      ∃ G : Finset (MvPolynomial (Fin n) k), (G : Set (MvPolynomial (Fin n) k)) ⊆ N ∧
        N ≤ frobSpan k p 0 (G : Set (MvPolynomial (Fin n) k)) ∧ FrobIndep G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro N hadd _ hpart
    refine ⟨∅, by simp, fun f hf => ?_, fun ψ _ _ g hg => absurd hg (Finset.notMem_empty g)⟩
    have : f = 0 := by
      rw [(hadd f hf).eq_sum_part]
      exact Finset.sum_eq_zero fun j _ => by
        rw [hpart f hf j (Finset.notMem_empty j), map_zero]
    rw [this]
    exact zero_mem _
  | insert j s hjs ih =>
    intro N hadd hfrob hpart
    set N' : Submodule k (MvPolynomial (Fin n) k) :=
      N ⊓ LinearMap.ker (part j : MvPolynomial (Fin n) k →ₐ[k] Polynomial k).toLinearMap
      with hN'
    have hmemN' : ∀ f, f ∈ N' ↔ f ∈ N ∧ part j f = 0 := fun f => Iff.rfl
    obtain ⟨G', hG'N, hNG', hG'ind⟩ := ih N' (fun f hf => hadd f ((hmemN' f).1 hf).1)
      (fun f hf => by
        obtain ⟨hfN, hfj⟩ := (hmemN' f).1 hf
        exact (hmemN' _).2 ⟨hfrob f hfN, by rw [map_pow, hfj, zero_pow hp.out.ne_zero]⟩)
      (fun f hf i hi => by
        obtain ⟨hfN, hfj⟩ := (hmemN' f).1 hf
        by_cases hij : i = j
        · rw [hij]
          exact hfj
        · exact hpart f hfN i (by simp [hij, hi]))
    by_cases hall : ∀ f ∈ N, part j f = 0
    · exact ⟨G', fun g hg => ((hmemN' g).1 (hG'N hg)).1,
        fun f hf => hNG' ((hmemN' f).2 ⟨hf, hall f hf⟩), hG'ind⟩
    push Not at hall
    have hex : ∃ d, ∃ f ∈ N, part j f ≠ 0 ∧ (part j f).natDegree = d := by
      obtain ⟨f, hf, hf0⟩ := hall
      exact ⟨_, f, hf, hf0, rfl⟩
    obtain ⟨h₀, hh₀N, hH0, hHd⟩ := Nat.find_spec hex
    have hH : IsAddPoly₁ (part j h₀) := (hadd h₀ hh₀N).isAddPoly₁_part j
    have hmin : ∀ f ∈ N, part j f ≠ 0 → (part j h₀).natDegree ≤ (part j f).natDegree := by
      intro f hf hf0
      rw [hHd]
      exact Nat.find_min' hex ⟨f, hf, hf0, rfl⟩
    have hdiv : ∀ f ∈ N, ∃ ψ : Polynomial k, IsAddPoly₁ ψ ∧ f - Polynomial.aeval h₀ ψ ∈ N' := by
      intro f hf
      obtain ⟨ψ, ρ, hψ, -, heq, hdeg⟩ :=
        hH.exists_comp_add (p := p) hH0 (part j f) ((hadd f hf).isAddPoly₁_part j)
      have hmem : f - Polynomial.aeval h₀ ψ ∈ N :=
        sub_mem hf (aeval_mem_of_frobClosed hfrob hh₀N hψ.mem_frobSpan₁)
      have hpartρ : part j (f - Polynomial.aeval h₀ ψ) = ρ := by
        rw [map_sub, part_aeval, heq]
        ring
      refine ⟨ψ, hψ, (hmemN' _).2 ⟨hmem, ?_⟩⟩
      rw [hpartρ]
      by_contra hρ0
      have h1 := hmin _ hmem (by rw [hpartρ]; exact hρ0)
      rw [hpartρ] at h1
      have h2 := Polynomial.natDegree_lt_natDegree hρ0 hdeg
      omega
    have hh₀G' : h₀ ∉ G' := fun h => hH0 ((hmemN' h₀).1 (hG'N h)).2
    refine ⟨insert h₀ G', ?_, ?_, ?_⟩
    · intro g hg
      rw [Finset.coe_insert] at hg
      rcases hg with rfl | hg
      · exact hh₀N
      · exact ((hmemN' g).1 (hG'N hg)).1
    · intro f hf
      obtain ⟨ψ, hψ, hmem⟩ := hdiv f hf
      have h1 : f - Polynomial.aeval h₀ ψ ∈
          frobSpan k p 0 ((insert h₀ G' : Finset _) : Set (MvPolynomial (Fin n) k)) :=
        frobSpan_mono (by rw [Finset.coe_insert]; exact Set.subset_insert _ _) (hNG' hmem)
      have h2 : Polynomial.aeval h₀ ψ ∈
          frobSpan k p 0 ((insert h₀ G' : Finset _) : Set (MvPolynomial (Fin n) k)) :=
        aeval_mem_frobSpan (by simp) hψ.mem_frobSpan₁
      simpa using add_mem h1 h2
    · intro ψ hψ hsum g hg
      rw [Finset.sum_insert hh₀G'] at hsum
      have hpartsum := congrArg (part j) hsum
      rw [map_add, map_sum, part_aeval, map_zero] at hpartsum
      have hzero : ∑ x ∈ G', part j (Polynomial.aeval x (ψ x)) = 0 :=
        Finset.sum_eq_zero fun x hx => by
          rw [part_aeval, ((hmemN' x).1 (hG'N hx)).2,
            (hψ x (Finset.mem_insert_of_mem hx)).comp_zero]
      rw [hzero, add_zero] at hpartsum
      have hψ0 : ψ h₀ = 0 := by
        by_contra hne
        exact (hψ h₀ (Finset.mem_insert_self _ _)).comp_ne_zero (p := p) hH hne hH0 hpartsum
      rw [hψ0, map_zero, zero_add] at hsum
      rw [Finset.mem_insert] at hg
      rcases hg with rfl | hg
      · exact hψ0
      · exact hG'ind ψ (fun g hg => hψ g (Finset.mem_insert_of_mem hg)) hsum g hg

/-- Purity turns Frobenius independence into linear independence of the linear terms:
a combination `∑ c_g • g` lying in the level-one Frobenius span has zero coefficients. -/
theorem FrobIndep.eq_zero_of_sum_smul_mem {G : Finset (MvPolynomial (Fin n) k)}
    (hG : FrobIndep G) (c : MvPolynomial (Fin n) k → k)
    (hc : ∑ g ∈ G, c g • g ∈ frobSpan k p 1 (G : Set (MvPolynomial (Fin n) k))) :
    ∀ g ∈ G, c g = 0 := by
  obtain ⟨ψ, hψ, heq⟩ := exists_eq_sum_of_mem_frobSpan hc
  have h := hG (fun g => c g • Polynomial.X - ψ g)
    (fun g _ => (isAddPoly₁_X.smul (c g)).sub
      (frobSpan₁_le_addPolys₁ (CharP.cast_eq_zero k p) 1 (hψ g)))
    (by simp only [map_sub, map_smul, Polynomial.aeval_X, Finset.sum_sub_distrib, ← heq,
      sub_self])
  intro g hg
  have := congrArg (fun φ => Polynomial.coeff φ 1) (h g hg)
  simpa [coeff_one_eq_zero_of_mem_frobSpan₁ (hψ g)] using this

end FrobeniusBasis

end Langlands.GroupScheme.TorusLinearization
