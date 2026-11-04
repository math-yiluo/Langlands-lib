import Langlands.GroupScheme.Rational.TorusWeightPrimitive

/-! # Graded polynomial coordinates on the first cyclic weight subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial

namespace Langlands.GroupScheme.Corepresented

section Coordinates

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- A polynomial that is weighted homogeneous of degree `j` vanishes at a point whose coordinates
of weight less than `r` vanish, if `0 < j < r` and all weights are positive. -/
theorem aeval_weightedHomogeneousComponent_eq_zero {ι A : Type*} [CommRing A] [Algebra k A]
    {d : ι → ℕ} {v : ι → A} {r j : ℕ} (hj0 : 0 < j) (hjr : j < r)
    (hv : ∀ i, d i < r → v i = 0) (p : MvPolynomial ι k) :
    aeval v (weightedHomogeneousComponent d j p) = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply, map_sum]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hμw : Finsupp.weight d μ = j := (Finset.mem_filter.mp hμ).2
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hμw
    exact hj0.ne hμw
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ0 (Finsupp.ext h)
  have hle : d i ≤ Finsupp.weight d μ := Finsupp.le_weight_of_ne_zero' d hi
  have hvi : v i = 0 := hv i (by omega)
  rw [aeval_monomial]
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
  change v i ^ μ i = 0
  rw [hvi, zero_pow hi]

/-- A weighted homogeneous polynomial of positive degree `r`, with positive weights, evaluated
at a point whose coordinates of weight less than `r` vanish, is the linear form given by its
coefficients at the variables of weight `r`. -/
theorem aeval_eq_sum_of_isWeightedHomogeneous {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] [Algebra k A] {d : ι → ℕ} (hd : ∀ i, 0 < d i) {r : ℕ} (hr : 0 < r)
    {p : MvPolynomial ι k} (hp : p.IsWeightedHomogeneous d r) {v : ι → A}
    (hv : ∀ i, d i < r → v i = 0) :
    aeval v p = ∑ j ∈ Finset.univ.filter (fun j => d j = r),
      algebraMap k A (p.coeff (Finsupp.single j 1)) * v j := by
  classical
  have key : ∀ μ ∈ p.support,
      aeval v (monomial μ (p.coeff μ)) = ∑ j ∈ Finset.univ.filter (fun j => d j = r),
        if μ = Finsupp.single j 1 then algebraMap k A (p.coeff μ) * v j else 0 := by
    intro μ hμ
    have hw : Finsupp.weight d μ = r := hp (mem_support_iff.mp hμ)
    rw [aeval_monomial]
    by_cases hs : ∃ j, μ = Finsupp.single j 1
    · obtain ⟨j₀, rfl⟩ := hs
      have hj₀ : d j₀ = r := by
        rw [← hw, Finsupp.weight_single, one_smul]
      rw [Finset.sum_eq_single j₀]
      · simp only [ite_true]
        rw [Finsupp.prod_single_index (h := fun i k => v i ^ k) (pow_zero (v j₀)), pow_one]
      · intro j _ hj
        have hne : Finsupp.single j₀ 1 ≠ Finsupp.single j 1 := fun h =>
          hj ((Finsupp.single_left_injective one_ne_zero) h).symm
        simp only [hne, ite_false]
      · intro h
        exact absurd (by simp [hj₀]) h
    · rw [Finset.sum_eq_zero fun j _ => by
        have hne : ¬ μ = Finsupp.single j 1 := fun h => hs ⟨j, h⟩
        simp only [hne, ite_false]]
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [map_zero] at hw
        exact hr.ne hw
      obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
        by_contra h
        push Not at h
        exact hμ0 (Finsupp.ext h)
      have hlt : ∃ i, μ i ≠ 0 ∧ d i < r := by
        by_contra h
        push Not at h
        apply hs
        refine ⟨j, Langlands.Algebra.GradedFormallySmooth.eq_single_of_weight_le hd hj ?_⟩
        rw [hw]
        exact h j hj
      obtain ⟨i, hi, hdi⟩ := hlt
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      change v i ^ μ i = 0
      rw [hv i hdi, zero_pow hi]
  conv_lhs => rw [p.as_sum, map_sum]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Finsupp.single j 1 ∈ p.support
  · rw [Finset.sum_eq_single (Finsupp.single j 1)]
    · simp only [ite_true]
    · intro μ _ hμ
      simp only [hμ, ite_false]
    · intro h
      exact absurd hj h
  · rw [Finset.sum_eq_zero fun μ hμ => by
      have hne : ¬ μ = Finsupp.single j 1 := fun h => hj (h ▸ hμ)
      simp only [hne, ite_false]]
    rw [notMem_support_iff.mp hj, map_zero, zero_mul]

/-- All weights of the coordinate algebra of a cyclic weight subgroup are multiples of `a`. -/
theorem comp_cyclicTail_mem_range {a : I → ℤ} (r : ℕ) :
    ∀ (g : B ⧸ weightIdeal e σ (cyclicTail a r)) m,
      comp (weightCorep e σ (cyclicTail a r)) (weightAction e σ (cyclicTail a r)) m g ≠ 0 →
        m ∈ Set.range (multiplesHom (I → ℤ) a) := by
  intro g m hg
  rcases (mem_insertZero _ m).1
      (mem_insertZero_of_comp_weightAction_ne_zero e σ (cyclicTail a r) g hg) with
    rfl | ⟨n, -, -, rfl⟩
  · exact ⟨0, zero_nsmul a⟩
  · exact ⟨n, rfl⟩

/-- In graded polynomial coordinates `x` (of positive weights `d i • a`) on the first cyclic
weight subgroup `U_1`, a point of `U_1` lies in `U_r` exactly when its coordinates of weight
less than `r` vanish. -/
theorem mem_weightSubgroup_iff_coord_eq_zero {a : I → ℤ} (ha : a ≠ 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)}
    (hd : ∀ i, 0 < d i)
    (hx : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
      (weightAction e σ (cyclicTail a 1)) (d i • a) (x i))
    (hsurj : Function.Surjective
      (aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ (cyclicTail a 1)))
    {A : CommAlgCat.{u} (CommRingCat.of k)}
    (u : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) {r : ℕ} :
    u.1 ∈ weightSubgroup e σ (cyclicTail a r) A ↔
      ∀ i, d i < r → coord (weightCorep e σ (cyclicTail a 1)) u (x i) = 0 := by
  constructor
  · intro h i hi
    obtain ⟨f, hf⟩ := exists_eq_mk_comp e σ (cyclicTail a 1) (hx i)
    rw [← hf, coord_cut_mk]
    have hnot : d i • a ∉ cyclicTail a r := by
      rintro ⟨n', hn', -, hna⟩
      have := nsmul_left_injective_of_ne_zero ha hna
      omega
    rw [(mem_weightSubgroup e σ _ _).1 h f _ hnot, counit_comp,
      ite_eq_right (nsmul_ne_zero_of_pos ha (hd i)), map_zero]
  · intro h
    refine (mem_weightSubgroup e σ _ _).2 fun f m hm => ?_
    by_cases hm1 : m ∈ cyclicTail a 1
    · obtain ⟨j, -, hj0, rfl⟩ := hm1
      have hjr : j < r := by
        by_contra hcon
        exact hm ⟨j, by omega, hj0, rfl⟩
      rw [counit_comp, ite_eq_right (nsmul_ne_zero_of_pos ha hj0), map_zero,
        ← coord_cut_mk (isCutOutBy_weightIdeal e σ (cyclicTail a 1)) u]
      have hφ : Function.Injective (multiplesHom (I → ℤ) a) :=
        nsmul_left_injective_of_ne_zero ha
      let _ := gradedAlgebra (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1)) hφ
        (comp_cyclicTail_mem_range e σ 1)
      let 𝒜 : ℕ → Submodule k (B ⧸ weightIdeal e σ (cyclicTail a 1)) := fun i =>
        homogeneousSubmodule (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1)) (multiplesHom (I → ℤ) a i)
      have hx' : ∀ i, x i ∈ 𝒜 (d i) := fun i => (mem_homogeneousSubmodule _ _ _ _).2 (hx i)
      have hg : Ideal.Quotient.mk (weightIdeal e σ (cyclicTail a 1)) (comp e σ (j • a) f) ∈ 𝒜 j := by
        refine (mem_homogeneousSubmodule _ _ _ _).2 ?_
        rw [← comp_restrict (isCutOutBy_weightIdeal e σ (cyclicTail a 1))
          (fun t _ hx => act_mem_weightSubgroup e σ (cyclicTail a 1) t hx)]
        exact isHomogeneous_comp _ _ _ _
      obtain ⟨p, hp⟩ := hsurj (Ideal.Quotient.mk (weightIdeal e σ (cyclicTail a 1)) (comp e σ (j • a) f))
      have h1 := Langlands.Algebra.GradedFormallySmooth.decompose_aeval 𝒜 hx' p j
      rw [hp, DirectSum.decompose_of_mem_same 𝒜 hg] at h1
      rw [h1, comp_aeval_apply]
      exact aeval_weightedHomogeneousComponent_eq_zero hj0 hjr h p
    · exact (mem_weightSubgroup e σ _ _).1 u.2 f m hm1

/-- On `U_r`, the graded coordinates of weight exactly `r` are additive. -/
theorem coord_mul_of_weight_eq {a : I → ℤ} (ha : a ≠ 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)}
    (hx : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
      (weightAction e σ (cyclicTail a 1)) (d i • a) (x i))
    {r : ℕ} (hr : 0 < r) {A : CommAlgCat.{u} (CommRingCat.of k)}
    {u u' : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A}
    (hu : u.1 ∈ weightSubgroup e σ (cyclicTail a r) A)
    (hu' : u'.1 ∈ weightSubgroup e σ (cyclicTail a r) A) {i : Fin n} (hi : d i = r) :
    coord (weightCorep e σ (cyclicTail a 1)) (u * u') (x i) =
      coord (weightCorep e σ (cyclicTail a 1)) u (x i) +
        coord (weightCorep e σ (cyclicTail a 1)) u' (x i) := by
  obtain ⟨f, hf⟩ := exists_eq_mk_comp e σ (cyclicTail a 1) (hx i)
  rw [← hf, coord_cut_mk, coord_cut_mk, coord_cut_mk, hi]
  exact coord_mul_comp_nsmul e σ ha hr hu hu' f

/-- Points of a corepresented functor whose coordinate algebra is generated by `x` are
determined by their values on `x`. -/
theorem coord_eq_of_apply_eq {F' : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {C : CommAlgCat.{u} (CommRingCat.of k)} (e' : (F' ⋙ forget GrpCat).CorepresentableBy C)
    {ι : Type*} {x : ι → C}
    (hsurj : Function.Surjective (aeval x : MvPolynomial ι k →ₐ[k] C))
    {A : CommAlgCat.{u} (CommRingCat.of k)} {u u' : F'.obj A}
    (h : ∀ i, coord e' u (x i) = coord e' u' (x i)) : u = u' := by
  apply coord_injective e'
  apply AlgHom.ext
  intro c
  obtain ⟨p, rfl⟩ := hsurj c
  rw [comp_aeval_apply, comp_aeval_apply]
  exact congrArg (fun v => aeval v p) (funext h)

/-- Points with prescribed values on free polynomial generators `x` of the coordinate
algebra exist. -/
theorem exists_coord_eq {F' : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
    {C : CommAlgCat.{u} (CommRingCat.of k)} (e' : (F' ⋙ forget GrpCat).CorepresentableBy C)
    {ι : Type*} {x : ι → C}
    (hbij : Function.Bijective (aeval x : MvPolynomial ι k →ₐ[k] C))
    {A : CommAlgCat.{u} (CommRingCat.of k)} (v : ι → A) :
    ∃ u : F'.obj A, ∀ i, coord e' u (x i) = v i := by
  let E : MvPolynomial ι k ≃ₐ[k] C := AlgEquiv.ofBijective (aeval x) hbij
  refine ⟨ofCoord e' ((aeval v).comp E.symm.toAlgHom), fun i => ?_⟩
  rw [coord_ofCoord, AlgHom.comp_apply]
  have : E.symm (x i) = X i := by
    apply E.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (aeval_X x i).symm
  change aeval v (E.symm (x i)) = v i
  rw [this, aeval_X]

/-- The graded coordinates of positive weight vanish at the identity. -/
theorem coord_one_of_isHomogeneous {a : I → ℤ} (ha : a ≠ 0) {m : ℕ} (hm : 0 < m)
    {g : B ⧸ weightIdeal e σ (cyclicTail a 1)}
    (hg : IsHomogeneous (weightCorep e σ (cyclicTail a 1)) (weightAction e σ (cyclicTail a 1))
      (m • a) g) {A : CommAlgCat.{u} (CommRingCat.of k)} :
    coord (weightCorep e σ (cyclicTail a 1))
      (1 : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A) g = 0 := by
  rw [coord_one, AlgHom.comp_apply, hg.counit_eq_zero (nsmul_ne_zero_of_pos ha hm), map_zero]

/-- Beyond the largest weight, the cyclic weight subgroups inside `U_1` are trivial. -/
theorem eq_one_of_mem_weightSubgroup_of_lt {a : I → ℤ} (ha : a ≠ 0)
    {n : ℕ} {d : Fin n → ℕ} {x : Fin n → B ⧸ weightIdeal e σ (cyclicTail a 1)}
    (hd : ∀ i, 0 < d i)
    (hx : ∀ i, IsHomogeneous (weightCorep e σ (cyclicTail a 1))
      (weightAction e σ (cyclicTail a 1)) (d i • a) (x i))
    (hsurj : Function.Surjective
      (aeval x : MvPolynomial (Fin n) k →ₐ[k] B ⧸ weightIdeal e σ (cyclicTail a 1)))
    {A : CommAlgCat.{u} (CommRingCat.of k)}
    {u : (cutFunctor (isCutOutBy_weightIdeal e σ (cyclicTail a 1))).obj A} {r : ℕ}
    (hr : ∀ i, d i < r) (hu : u.1 ∈ weightSubgroup e σ (cyclicTail a r) A) : u = 1 := by
  have h := (mem_weightSubgroup_iff_coord_eq_zero e σ ha hd hx hsurj u).1 hu
  refine coord_eq_of_apply_eq (weightCorep e σ (cyclicTail a 1)) hsurj fun i => ?_
  rw [h i (hr i), coord_one_of_isHomogeneous e σ ha (hd i) (hx i)]

end Coordinates

end Langlands.GroupScheme.Corepresented
