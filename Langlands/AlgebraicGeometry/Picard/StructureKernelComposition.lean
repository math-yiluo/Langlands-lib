import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Picard.SquareZeroAmbientObstructionNaturality
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange

/-! # Actual structure-kernel maps under a factorization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.StructureKernelModule

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X Y Z : Scheme.{u}} (j : Z ⟶ Y) (h : Y ⟶ X)

/-- Restrict an actual composite-kernel section through the intermediate structure map. -/
def compositionMap :
    kernelModule (j ≫ h) ⟶ (Scheme.Modules.pushforward h).obj (kernelModule j) :=
  SquareZeroAmbientObstructionNaturality.kernelModuleMap h j

@[simp]
lemma compositionMap_app (U : X.Opens) (a : Γ(kernelModule (j ≫ h), U)) :
    ((compositionMap j h).app U a).val = h.app U a.val := rfl

/-- The kernel map is the restriction of the actual intermediate structure map. -/
@[reassoc]
lemma compositionMap_ι :
    compositionMap j h ≫ (Scheme.Modules.pushforward h).map (kernelModuleι j) =
      kernelModuleι (j ≫ h) ≫ unitToPushforwardUnit h := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  rfl

/-- The relative cohomology map of an actual factorization over affine bases. -/
def compositionCohomologyMap [IsAffineHom h] [IsAffineHom j]
    {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (p : X ⟶ Spec R) (p' : Y ⟶ Spec S)
    (w : h ≫ p = p' ≫ Spec.map φ) (n : ℕ) :
    (relativeCohomology p n).obj (kernelModule (j ≫ h)) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((relativeCohomology p' n).obj (kernelModule j)) := by
  letI : (kernelModule j).IsQuasicoherent := kernelModule_isQuasicoherent j
  exact (relativeCohomology p n).map (compositionMap j h) ≫
    (affinePushforwardCohomologyIso h p (kernelModule j) n).inv ≫
    (relativeCohomologyBaseRingIso φ (h ≫ p) p' w n).hom.app (kernelModule j)

end Langlands.AlgebraicGeometry.Picard.StructureKernelModule
