import Langlands.AlgebraicGeometry.Picard.MumfordSchemeMapHomomorphismStatement
import Langlands.AlgebraicGeometry.Picard.MumfordUnit
import Langlands.AlgebraicGeometry.Picard.MumfordBundleParameterAdditivityProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs

/-! # The homomorphism equations for the actual Mumford map -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The actual Mumford classifying morphism preserves the unit and
multiplication over every quasi-separated base. -/
theorem relativeMumfordSchemeMapHomomorphism :
    RelativeMumfordSchemeMapHomomorphismStatement.{u} := by
  intro preservation stability square S _ A L M evaluation hA
  constructor
  · exact mumfordSchemeMap_unit A preservation L M evaluation stability square hA
  · apply dualPointClass_injective stability A hA
    rw [dualTensor_points stability A hA preservation
      pullbackTensorComposition pullbackTensorLeftUnitor]
    apply Subtype.ext
    change RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
      (poincareFamily A hA) _ (μ[A.X] ≫ _) =
        RigidifiedLineBundle.classesTensor preservation A.X.hom (unitSection A)
          (unitSection_comp A) _
          (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
            (poincareFamily A hA) _ (CartesianMonoidalCategory.fst A.X A.X ≫ _))
          (RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
            (poincareFamily A hA) _ (CartesianMonoidalCategory.snd A.X A.X ≫ _))
    rw [mumfordSchemeMap_points, mumfordSchemeMap_points, mumfordSchemeMap_points]
    exact mumfordBundleParameterAdditivity preservation S A L M evaluation

end Langlands.AbelianScheme
