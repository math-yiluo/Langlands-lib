import Langlands.Representation.Plancherel.RationalAmbientBlockScaling
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryScalarStatement
import Mathlib.Topology.Algebra.Polynomial

/-! # A unitary coordinate on the primitive rank-one valuation kernel -/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel.ValuationKernelCoordinates

section DenseBound

variable {X : Type*} [TopologicalSpace X]

/-- A bound on a dense set of actual parameters gives the same bound at every
nonpole of a continuous surjective circle coordinate. -/
theorem circle_quotient_bound_of_dense
    (t : X → Circle) (ht : Continuous t) (hsurj : Function.Surjective t)
    (D : Set X) (hD : Dense D) (p q : Polynomial ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ D, q.eval (t x : ℂ) ≠ 0 →
      ‖p.eval (t x : ℂ) / q.eval (t x : ℂ)‖ ≤ C) :
    ∀ z : Circle, q.eval (z : ℂ) ≠ 0 →
      ‖p.eval (z : ℂ) / q.eval (z : ℂ)‖ ≤ C := by
  intro z hz
  obtain ⟨x, rfl⟩ := hsurj z
  let f : X → ℂ := fun y => p.eval (t y : ℂ) / q.eval (t y : ℂ)
  have hf : ContinuousAt f x :=
    ((p.continuous.comp (continuous_subtype_val.comp ht)).continuousAt).div
      ((q.continuous.comp (continuous_subtype_val.comp ht)).continuousAt) hz
  have himage : f '' D ⊆ {w : ℂ | ‖w‖ ≤ C} := by
    rintro _ ⟨y, hy, rfl⟩
    change ‖f y‖ ≤ C
    by_cases hq : q.eval (t y : ℂ) = 0
    · simpa only [f, hq, div_zero, norm_zero] using hC
    · exact hbound y hy hq
  have hclosed : IsClosed {w : ℂ | ‖w‖ ≤ C} :=
    isClosed_le continuous_norm continuous_const
  exact (closure_minimal himage hclosed) (mem_closure_image hf (hD x))

end DenseBound

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]

local instance kernelUnitaryPointTopology : TopologicalSpace (rationalPoints H) :=
  rationalPointTopology F H.X

variable {n : ℕ}
  (e : Additive (rationalDiscreteValuationImage H) ≃ₗ[ℤ]
    (Fin 1 → ℤ) × (Fin n → ℤ))

/-- The primitive first-coordinate element of the actual valuation lattice. -/
def firstGenerator : Additive (rationalDiscreteValuationImage H) :=
  e.symm (Pi.single (0 : Fin 1) 1, 0)

/-- A unitary image character with a prescribed first coordinate and trivial
complement coordinates. -/
def firstImageUnitaryCharacter (z : Circle) : rationalUnitaryImageCharacters H where
  toFun a := z ^ (e (Additive.ofMul a)).1 0
  map_one' := by
    change z ^ (e 0).1 0 = 1
    simp
  map_mul' a b := by
    change z ^ (e (Additive.ofMul a + Additive.ofMul b)).1 0 = _
    simp [zpow_add]
  continuous_toFun := continuous_of_discreteTopology

/-- Project an actual unitary parameter to its first coordinate. -/
def firstUnitaryCoordinate
    (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    Circle :=
  (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).symm chi
    (firstGenerator e).toMul

theorem continuous_firstUnitaryCoordinate : Continuous (firstUnitaryCoordinate e) := by
  have hc : Continuous (fun xi : rationalDiscreteValuationImage H →ₜ* Circle =>
      xi (firstGenerator e).toMul) := continuous_eval_const _
  exact hc.comp
    (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).symm.continuous

/-- Every circle point occurs on the actual unitary unramified subgroup. -/
theorem firstUnitaryCoordinate_surjective :
    Function.Surjective (firstUnitaryCoordinate e) := by
  intro z
  refine ⟨rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H
    (firstImageUnitaryCharacter e z), ?_⟩
  change (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).symm
    (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H
      (firstImageUnitaryCharacter e z)) (firstGenerator e).toMul = z
  rw [ContinuousMulEquiv.symm_apply_apply]
  change z ^ (e (e.symm (Pi.single (0 : Fin 1) 1, 0))).1 0 = z
  simp

/-- The exact first Laurent monomial in the existing actual regular algebra. -/
def firstRegularCoordinate :
    unramifiedRegularFunctions (fun psi => (rationalNormCharacters H psi).toMul) :=
  productLaurentAlgebraEquiv e
    (AddMonoidAlgebra.single (Pi.single (0 : Fin 1) 1, 0) 1)

/-- Regular and unitary first coordinates have the same actual value. -/
theorem firstRegularCoordinate_eval_unitary
    (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    (firstRegularCoordinate e).val ⟨chi.val, chi.property.1⟩ =
      (firstUnitaryCoordinate e chi : ℂ) := by
  rw [firstRegularCoordinate, productLaurentAlgebraEquiv_single_eval, one_mul]
  obtain ⟨h, hh⟩ := rationalValuationImageProjection_surjective H (firstGenerator e).toMul
  change (rationalImageUnramifiedDescend H ⟨chi.val, chi.property.1⟩
    (firstGenerator e).toMul : ℂ) = _
  rw [← hh, rationalImageUnramifiedDescend_projection]
  let xi := (rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).symm chi
  have hc := congrArg (fun y => ((y.val h : ℂˣ) : ℂ))
    ((rationalCanonicalUnitaryImageUnramifiedContinuousEquiv H).apply_symm_apply chi)
  rw [rationalCanonicalUnitaryImageUnramifiedContinuousEquiv_apply, hh] at hc
  exact hc.symm

/-- Substitute the actual first-coordinate regular function into a polynomial. -/
def firstPolynomialMap :
    Polynomial ℂ →ₐ[ℂ]
      unramifiedRegularFunctions (fun psi => (rationalNormCharacters H psi).toMul) :=
  Polynomial.aeval (firstRegularCoordinate e)

theorem firstPolynomialMap_eval
    (p : Polynomial ℂ)
    (chi : unramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    (firstPolynomialMap e p).val chi = p.eval ((firstRegularCoordinate e).val chi) := by
  change ((Polynomial.aeval (firstRegularCoordinate e) p).val chi) = _
  rw [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_fn_apply]
  rfl

theorem firstPolynomialMap_eval_unitary
    (p : Polynomial ℂ)
    (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul)) :
    (firstPolynomialMap e p).val ⟨chi.val, chi.property.1⟩ =
      p.eval (firstUnitaryCoordinate e chi : ℂ) := by
  rw [firstPolynomialMap_eval, firstRegularCoordinate_eval_unitary]

/-- A polynomial fraction in this actual coordinate is algebraically regular
at every unitary parameter at which the univariate denominator is nonzero. -/
theorem regularAt_of_firstPolynomialFraction
    (hH : IsConnectedReductive H) (p q : Polynomial ℂ)
    (f : rationalUnramifiedFunctionField H
      (continuous_rationalValuationImageProjection H) hH)
    (hf : f = algebraMap _
        (rationalUnramifiedFunctionField H (continuous_rationalValuationImageProjection H) hH)
          (firstPolynomialMap e p) /
      algebraMap _
        (rationalUnramifiedFunctionField H (continuous_rationalValuationImageProjection H) hH)
          (firstPolynomialMap e q))
    (chi : unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters H psi).toMul))
    (hq : q.eval (firstUnitaryCoordinate e chi : ℂ) ≠ 0) :
    RationalFunctionRegularAt H (continuous_rationalValuationImageProjection H) hH f
      ⟨chi.val, chi.property.1⟩ := by
  refine ⟨firstPolynomialMap e p, firstPolynomialMap e q, ?_, hf⟩
  rwa [firstPolynomialMap_eval_unitary]

/-- Transfer a dense actual unitary bound on a first-coordinate polynomial
fraction to every circle point where its denominator is nonzero. -/
theorem firstPolynomialFraction_circle_bound_of_dense
    (D : Set (unitaryUnramifiedCharacters
      (fun psi => (rationalNormCharacters H psi).toMul)))
    (hD : Dense D) (p q : Polynomial ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ chi ∈ D,
      (firstPolynomialMap e q).val ⟨chi.val, chi.property.1⟩ ≠ 0 →
      ‖(firstPolynomialMap e p).val ⟨chi.val, chi.property.1⟩ /
        (firstPolynomialMap e q).val ⟨chi.val, chi.property.1⟩‖ ≤ C) :
    ∀ z : Circle, q.eval (z : ℂ) ≠ 0 →
      ‖p.eval (z : ℂ) / q.eval (z : ℂ)‖ ≤ C := by
  apply circle_quotient_bound_of_dense (firstUnitaryCoordinate e)
    (continuous_firstUnitaryCoordinate e) (firstUnitaryCoordinate_surjective e)
    D hD p q C hC
  intro chi hchi hq
  have hb := hbound chi hchi
  simp only [firstPolynomialMap_eval_unitary] at hb
  exact hb hq

end Langlands.Plancherel.ValuationKernelCoordinates
