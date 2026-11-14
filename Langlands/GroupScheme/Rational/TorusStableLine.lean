import Langlands.GroupScheme.Rational.TorusGrading
import Langlands.CommutativeAlgebra.GradedLineFlatLocal

/-! # Weights of stable coordinate lines over local rings -/

noncomputable section

universe u

open CategoryTheory Polynomial

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

/-- A free coordinate line stable under the weight projections over a local ring
is a single weight space. -/
theorem exists_isHomogeneous_of_stable_line [IsLocalRing R] {x : B}
    (hfaithful : Function.Injective (fun r : R => r • x))
    (hstable : ∀ m : I → ℤ, comp e σ m x ∈ Submodule.span R {x}) :
    ∃ m : I → ℤ, IsHomogeneous e σ m x := by
  classical
  choose r hr using fun m => Submodule.mem_span_singleton.mp (hstable m)
  have hsum : ∑ m ∈ (rho e σ x).coeff.support, r m = (1 : R) := by
    apply hfaithful
    dsimp only
    rw [Finset.sum_smul, one_smul]
    simpa only [hr] using sum_support_comp e σ x
  obtain ⟨m, _, u, hu⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one)
  refine ⟨m, ?_⟩
  have hm := (isHomogeneous_comp e σ m x).smul (↑(u⁻¹) : R)
  rw [← hr m, ← hu, smul_smul, Units.inv_mul, one_smul] at hm
  exact hm

end Langlands.GroupScheme.Corepresented

namespace Langlands.CommutativeAlgebra.GradedLine

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
  {c : A →+* LaurentPolynomial A} (hc : IsGrading R c)

/-- The degree of a positive homogeneous polynomial generator has rank one. -/
theorem homog_eq_span_of_aeval_surjective {d : ℕ} (hd : 0 < d) {x : A}
    (hx : x ∈ homog hc d)
    (hgen : Function.Surjective (Polynomial.aeval x : R[X] →ₐ[R] A)) :
    homog hc d = Submodule.span R {x} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨p, rfl⟩ := hgen y
    have h := comp_aeval hc hd hx p 1
    simp only [Nat.cast_one, one_mul, pow_one] at h
    rw [comp_self hc hy] at h
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)

/-- The scalar multiples of a polynomial coordinate form a free line. -/
theorem smul_injective_of_aeval_injective {x : A}
    (hx : Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A)) :
    Function.Injective (fun r : R => r • x) := by
  intro r s h
  have heq : Polynomial.aeval x (Polynomial.C r * Polynomial.X) =
      Polynomial.aeval x (Polynomial.C s * Polynomial.X) := by
    simpa only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Algebra.smul_def] using h
  have hpoly := congrArg (fun p : R[X] => p.coeff 1) (hx heq)
  simpa using hpoly

end Langlands.CommutativeAlgebra.GradedLine

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)
  {c : B →+* LaurentPolynomial B} (hc : CommutativeAlgebra.GradedLine.IsGrading R c)

/-- Preserving the degree of a positive homogeneous polynomial coordinate forces
the torus to act on that coordinate through one character. -/
theorem exists_isHomogeneous_of_preserves_degree [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : B} (hx : x ∈ CommutativeAlgebra.GradedLine.homog hc d)
    (hgen : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] B))
    (hstable : ∀ m : I → ℤ,
      comp e σ m x ∈ CommutativeAlgebra.GradedLine.homog hc d) :
    ∃ m : I → ℤ, IsHomogeneous e σ m x := by
  apply exists_isHomogeneous_of_stable_line e σ
    (CommutativeAlgebra.GradedLine.smul_injective_of_aeval_injective hgen.1)
  intro m
  rw [← CommutativeAlgebra.GradedLine.homog_eq_span_of_aeval_surjective hc hd hx hgen.2]
  exact hstable m

/-- A chosen torus weight of a polynomial coordinate whose degree is preserved. -/
def coordinateWeightOfPreservesDegree [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : B} (hx : x ∈ CommutativeAlgebra.GradedLine.homog hc d)
    (hgen : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] B))
    (hstable : ∀ m : I → ℤ,
      comp e σ m x ∈ CommutativeAlgebra.GradedLine.homog hc d) : I → ℤ :=
  (exists_isHomogeneous_of_preserves_degree e σ hc hd hx hgen hstable).choose

/-- The chosen weight is the actual weight of the coordinate. -/
theorem isHomogeneous_coordinateWeightOfPreservesDegree [IsLocalRing R] {d : ℕ} (hd : 0 < d)
    {x : B} (hx : x ∈ CommutativeAlgebra.GradedLine.homog hc d)
    (hgen : Function.Bijective (Polynomial.aeval x : R[X] →ₐ[R] B))
    (hstable : ∀ m : I → ℤ,
      comp e σ m x ∈ CommutativeAlgebra.GradedLine.homog hc d) :
    IsHomogeneous e σ (coordinateWeightOfPreservesDegree e σ hc hd hx hgen hstable) x :=
  (exists_isHomogeneous_of_preserves_degree e σ hc hd hx hgen hstable).choose_spec

end Langlands.GroupScheme.Corepresented
