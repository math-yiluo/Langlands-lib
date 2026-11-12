import Langlands.AbelianScheme.FieldSymmetricAmpleExistenceStatement
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AbelianScheme.MultiplicationSign
import Langlands.AlgebraicGeometry.Picard.AmpleTensorProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Symmetric ample line bundles over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Symmetrizing an ample line bundle by inversion gives an actual symmetric
ample line bundle on every commutative smooth proper geometrically connected
group scheme over an arbitrary field. -/
theorem fieldSymmetricAmpleExistence : FieldSymmetricAmpleExistenceStatement.{u} := by
  intro K _ G _ hSmooth hProper hConnected
  obtain ⟨M, hM⟩ := fieldAmpleExistence K G hSmooth hProper hConnected
  let f := (multiplication G (-1)).hom.hom.left
  let e : G.X.left ≅ G.X.left :=
    (Grp.forget (Over (Spec (CommRingCat.of K))) ⋙
      Over.forget (Spec (CommRingCat.of K))).mapIso (multiplicationNegOneIso G)
  have hf : f ≫ f = 𝟙 G.X.left := e.hom_inv_id
  let : IsIso f := inferInstanceAs (IsIso e.hom)
  let N := (LineBundle.pullback f).obj M
  let L := LineBundle.tensor pullbackTensorComparisonIsIso M N
  refine ⟨L, ampleTensor _ M N L ⟨Iso.refl _⟩ hM
    (closedImmersionPullbackAmple _ _ f M inferInstance hM), ⟨?_⟩⟩
  change (Scheme.Modules.pullback f).obj (tensorObj M.obj N.obj) ≅
    tensorObj M.obj N.obj
  letI := pullbackTensorComparisonIsIso f
  let e₂ : (Scheme.Modules.pullback f).obj N.obj ≅ M.obj :=
    (Scheme.Modules.pullbackComp f f).app M.obj ≪≫
      (Scheme.Modules.pullbackCongr hf).app M.obj ≪≫
        (Scheme.Modules.pullbackId G.X.left).app M.obj
  exact (asIso (pullbackTensorComparison f)).app (M.obj, N.obj) ≪≫
    (tensorFunctor G.X.left).mapIso ((Iso.refl N.obj).prod e₂) ≪≫
      tensorComm N.obj M.obj

end Langlands.GroupScheme
