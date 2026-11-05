import Langlands.GroupScheme.IntegralModel.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Model homomorphisms over a coefficient square -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}
  {M : IntegralModel R K G} {N : IntegralModel R K H} {f : G ⟶ H}
  (φ : M.Hom N f)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]

/-- Change the integral and generic coefficients of an actual compatible homomorphism. -/
def Hom.baseChangeCoefficients :
    (M.baseChange A L).Hom (N.baseChange A L)
      ((GroupScheme.baseChange (Spec.algebraMap K L)).map f) where
  hom := (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.hom
  generic_comm := M.baseChangeGenericIso_naturality A L N φ

/-- The changed homomorphism is the actual pullback of the original homomorphism. -/
theorem Hom.baseChangeCoefficients_hom :
    (φ.baseChangeCoefficients A L).hom =
      (GroupScheme.baseChange (Spec.algebraMap R A)).map φ.hom := rfl

/-- A closed inclusion remains closed under the same coefficient square. -/
theorem Hom.isClosedImmersion_baseChangeCoefficients
    (hφ : IsClosedImmersion φ.hom.hom.hom.left) :
    IsClosedImmersion (φ.baseChangeCoefficients A L).hom.hom.hom.left :=
  IsClosedSubgroup.baseChange (Spec.algebraMap R A) hφ

end Langlands.GroupScheme.IntegralModel
