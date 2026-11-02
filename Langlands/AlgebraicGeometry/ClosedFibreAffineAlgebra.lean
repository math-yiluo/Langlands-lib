import Langlands.AlgebraicGeometry.ClosedFibreOpenIntegrality
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # The actual algebras of affine closed-fibre neighbourhoods -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} (hU : IsAffineOpen U)

/-- The coefficient algebra on the actual sections of an affine source open,
recovered from its actual structure morphism. -/
@[instance_reducible]
def affineSectionAlgebra : Algebra R Γ(X, U) :=
  (Spec.homEquiv (hU.fromSpec ≫ p)).hom.toAlgebra

/-- The spectrum map for the chosen algebra is the original affine chart map. -/
theorem affineSectionAlgebra_specMap :
    letI := affineSectionAlgebra p hU
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ p := by
  exact Spec.homEquiv.symm_apply_apply (hU.fromSpec ≫ p)

/-- Local finite presentation of a scheme morphism gives algebra finite
presentation of the actual sections on every affine source open. -/
theorem finitePresentation_affineSectionAlgebra [LocallyOfFinitePresentation p] :
    letI := affineSectionAlgebra p hU
    Algebra.FinitePresentation R Γ(X, U) := by
  let := affineSectionAlgebra p hU
  apply RingHom.finitePresentation_algebraMap.mp
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mp
  change LocallyOfFinitePresentation
    (Spec.homEquiv.symm (Spec.homEquiv (hU.fromSpec ≫ p)))
  rw [Spec.homEquiv.symm_apply_apply]
  infer_instance

/-- Flatness of a scheme morphism gives flatness of the actual affine
section algebra over the original base ring. -/
theorem flat_affineSectionAlgebra [Flat p] :
    letI := affineSectionAlgebra p hU
    Module.Flat R Γ(X, U) := by
  let := affineSectionAlgebra p hU
  apply RingHom.flat_algebraMap_iff.mp
  apply Flat.SpecMap_iff.mp
  change Flat (Spec.homEquiv.symm (Spec.homEquiv (hU.fromSpec ≫ p)))
  rw [Spec.homEquiv.symm_apply_apply]
  infer_instance

/-- An affine chart meeting the closed fibre has a geometrically integral
actual spectrum map for its chosen coefficient algebra. -/
theorem geometricallyIntegral_affineSectionAlgebra [IsLocalRing R]
    [Smooth p] [GeometricallyConnected p]
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty) :
    letI := affineSectionAlgebra p hU
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U)))) := by
  let := affineSectionAlgebra p hU
  rw [affineSectionAlgebra_specMap p hU, IsAffineOpen.fromSpec, Category.assoc]
  apply (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral
    hU.isoSpec.inv (U.ι ≫ p)).mpr
  exact geometricallyIntegral_open_of_meets_closedFibre p U hmeet

/-- Geometric integrality of an algebra's spectrum map makes its actual
closed-fibre ideal prime. No flatness or smoothness is needed here. -/
theorem closedFibreIdeal_isPrime_of_geometricallyIntegral
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing R]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R A)))] :
    ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime := by
  let k := R ⧸ IsLocalRing.maximalIdeal R
  let : Field k := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R k))
  let : IsIntegral (pullback f b) :=
    pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := f)) k b
  let : IsIntegral (Spec (CommRingCat.of (A ⊗[R] k))) :=
    IsIntegral.of_isIso (pullbackSpecIso R A k).hom
  let : IsDomain (A ⊗[R] k) :=
    (affine_isIntegral_iff (CommRingCat.of (A ⊗[R] k))).mp inferInstance
  let : IsDomain (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A
      (IsLocalRing.maximalIdeal R)).toRingEquiv.toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

/-- The actual closed fibre of the section algebra on an affine open
meeting the closed fibre is a domain. -/
theorem closedFibreIdeal_isPrime_affineSectionAlgebra [IsLocalRing R]
    [Smooth p] [GeometricallyConnected p]
    (hmeet : (p ⁻¹' {IsLocalRing.closedPoint R} ∩ (U : Set X)).Nonempty) :
    letI := affineSectionAlgebra p hU
    ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(X, U))).IsPrime := by
  let := affineSectionAlgebra p hU
  let := geometricallyIntegral_affineSectionAlgebra p hU hmeet
  exact closedFibreIdeal_isPrime_of_geometricallyIntegral

end Langlands.AlgebraicGeometry
