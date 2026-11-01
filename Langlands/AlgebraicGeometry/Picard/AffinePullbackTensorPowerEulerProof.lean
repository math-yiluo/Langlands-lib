import Langlands.AlgebraicGeometry.Picard.AffinePullbackTensorPowerEulerStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleProjectionFormulaProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof

/-! # Affine cohomology after the actual line-bundle projection formula -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The actual tensor-power projection isomorphism for a line bundle. -/
def lineBundleTensorPowerProjectionIso {X Y : Scheme.{u}}
    (f : X ⟶ Y) (L : LineBundle Y) (n : ℕ) :
    tensorObj (tensorPow L.obj n)
        ((Scheme.Modules.pushforward f).obj (structureSheaf X)) ≅
      (Scheme.Modules.pushforward f).obj
        (tensorPow ((Scheme.Modules.pullback f).obj L.obj) n) := by
  let Ln : LineBundle Y := ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne Y L n⟩
  exact lineBundleProjectionIso f Ln (structureSheaf X) ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (tensorRightUnitor _ ≪≫ actualPullbackTensorPowIso f L.obj n)

/-- Affine pullback tensor powers and tensoring with the structure-module
pushforward have the same actual finite cohomology and Euler value. -/
theorem affinePullbackTensorPowerEuler :
    AffinePullbackTensorPowerEulerStatement.{u} := by
  intro K _ X Y f hf s L n
  let : IsAffineHom f := hf
  let A := tensorPow ((Scheme.Modules.pullback f).obj L.obj) n
  let B := tensorObj (tensorPow L.obj n)
    ((Scheme.Modules.pushforward f).obj (structureSheaf X))
  let E := lineBundleTensorPowerProjectionIso f L n
  have hq : A.IsQuasicoherent :=
    (tensorPow_isLocallyFreeRankOne X ((LineBundle.pullback f).obj L) n).isQuasicoherent
  have h := affinePushforwardEulerCharacteristic K X Y f hf s A hq
  have hBP : HasFiniteCohomology s B ↔
      HasFiniteCohomology s ((Scheme.Modules.pushforward f).obj A) :=
    ⟨hasFiniteCohomology_of_iso s E, hasFiniteCohomology_of_iso s E.symm⟩
  refine ⟨h.1.trans hBP.symm, ?_⟩
  intro hA hB
  exact (h.2 hA (h.1.mp hA)).trans
    (eulerCharacteristic_eq_of_iso s hB (h.1.mp hA) E).symm

end Langlands.AlgebraicGeometry.Picard
