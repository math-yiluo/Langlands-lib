import Langlands.GroupScheme.Rational.CyclicWeightConjugation

/-! # Intrinsic cyclic cutoffs in nonnegative polynomial coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- Polynomial generators of nonnegative integral cyclic weights, vanishing at
the identity. Zero weights are permitted over the arbitrary base ring. -/
structure NonnegativeCyclicCoordinates (a : I → ℤ) where
  dimension : ℕ
  weight : Fin dimension → ℕ
  generator : Fin dimension → B
  homogeneous : ∀ i, IsHomogeneous e σ (weight i • a) (generator i)
  augmented : ∀ i, AffineLinearEmbedding.counit e (generator i) = 0
  surjective : Function.Surjective (aeval generator :
    MvPolynomial (Fin dimension) R →ₐ[R] B)

namespace NonnegativeCyclicCoordinates

variable {e σ} {a : I → ℤ} (C : NonnegativeCyclicCoordinates e σ a)

private theorem weight_cyclic (μ : Fin C.dimension →₀ ℕ) :
    Finsupp.weight (fun i => C.weight i • a) μ = Finsupp.weight C.weight μ • a := by
  ext j
  simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    nsmul_eq_mul, Finset.sum_mul, mul_assoc]

private theorem homogeneous_monomial (μ : Fin C.dimension →₀ ℕ) (c : R) :
    IsHomogeneous e σ (Finsupp.weight C.weight μ • a)
      (aeval C.generator (monomial μ c)) := by
  let _ := weightGradedAlgebra e σ
  rw [← C.weight_cyclic μ]
  apply (mem_homogeneousSubmodule _ _ _ _).1
  rw [aeval_monomial, ← Algebra.smul_def, Finsupp.weight_apply]
  exact Submodule.smul_mem _ c
    (SetLike.prod_pow_mem_graded (homogeneousSubmodule e σ)
      (fun i => C.weight i • a) C.generator μ
      (fun i _ => (mem_homogeneousSubmodule _ _ _ _).2 (C.homogeneous i)))

private theorem eval_monomial_eq_zero {A : CommAlgCat.{u} R} (x : F.obj A)
    {r : ℕ} (hx : ∀ i, C.weight i < r → coord e x (C.generator i) = 0)
    {μ : Fin C.dimension →₀ ℕ} (hμ : μ ≠ 0)
    (hμr : Finsupp.weight C.weight μ < r) (c : R) :
    coord e x (aeval C.generator (monomial μ c)) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (Finsupp.ext h)
  have hdi : C.weight i < r :=
    lt_of_le_of_lt (Finsupp.le_weight_of_ne_zero' C.weight hi) hμr
  rw [aeval_monomial, map_mul]
  apply mul_eq_zero_of_right
  rw [map_finsuppProd]
  apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
  change coord e x (C.generator i ^ μ i) = 0
  rw [map_pow, hx i hdi, zero_pow hi]

private theorem counit_monomial_eq_zero {μ : Fin C.dimension →₀ ℕ}
    (hμ : μ ≠ 0) (c : R) :
    AffineLinearEmbedding.counit e (aeval C.generator (monomial μ c)) = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (Finsupp.ext h)
  rw [aeval_monomial, map_mul]
  apply mul_eq_zero_of_right
  rw [map_finsuppProd]
  apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
  change AffineLinearEmbedding.counit e (C.generator i ^ μ i) = 0
  rw [map_pow, C.augmented i, zero_pow hi]

/-- Every positive intrinsic cutoff is exactly the coordinate subspace obtained
by vanishing all generators of smaller weight, including zero-weight ones. -/
theorem mem_iff (ha : a ≠ 0) {A : CommAlgCat.{u} R} (x : F.obj A)
    {r : ℕ} (hr : 0 < r) :
    x ∈ weightSubgroup e σ (cyclicTail a r) A ↔
      ∀ i, C.weight i < r → coord e x (C.generator i) = 0 := by
  constructor
  · intro hx i hi
    have hnot : C.weight i • a ∉ cyclicTail a r := by
      rintro ⟨n, hn, -, hna⟩
      have h := nsmul_left_injective_of_ne_zero ha hna
      omega
    have h := (mem_weightSubgroup e σ _ x).1 hx (C.generator i)
      (C.weight i • a) hnot
    rwa [(C.homogeneous i).comp_self, C.augmented i, map_zero] at h
  · intro hx
    refine (mem_weightSubgroup e σ _ x).2 fun f m hm => ?_
    obtain ⟨p, rfl⟩ := C.surjective f
    induction p using MvPolynomial.induction_on' with
    | monomial μ c =>
      rw [(C.homogeneous_monomial μ c).comp_eq]
      split_ifs with hdeg
      · by_cases hμ : μ = 0
        · subst hμ
          simp only [aeval_monomial, Finsupp.prod_zero_index, mul_one]
          simp [AlgHom.commutes]
        · have hlt : Finsupp.weight C.weight μ < r := by
            by_contra h
            exact hm ⟨Finsupp.weight C.weight μ, by omega,
              lt_of_lt_of_le hr (by omega), hdeg.symm⟩
          rw [C.eval_monomial_eq_zero x hx hμ hlt c,
            C.counit_monomial_eq_zero hμ c, map_zero]
      · rw [map_zero, map_zero, map_zero]
    | add p q hp hq =>
      simp only [map_add, hp, hq]

/-- Intrinsic cyclic cutoffs, described by these coordinates, are preserved by
conjugators with constant twisted orbit. -/
theorem low_coordinates_conjugate (ha : a ≠ 0) {A : CommAlgCat.{u} R}
    {r : ℕ} (hr : 0 < r) (z x : F.obj A)
    (hz : hat σ z = F.map (constHom I A) z)
    (hx : ∀ i, C.weight i < r → coord e x (C.generator i) = 0) :
    ∀ i, C.weight i < r → coord e (z * x * z⁻¹) (C.generator i) = 0 :=
  (C.mem_iff ha _ hr).1
    (conj_mem_weightSubgroup_of_hat_eq e σ _ hz ((C.mem_iff ha x hr).2 hx))

end NonnegativeCyclicCoordinates

end Langlands.GroupScheme.Corepresented
