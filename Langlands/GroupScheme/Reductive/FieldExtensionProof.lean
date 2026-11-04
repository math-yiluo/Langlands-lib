import Langlands.GroupScheme.Reductive.FieldExtensionStatement
import Langlands.GroupScheme.Reductive.RadicalFieldExtensionProof
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Connected reductivity under arbitrary field extension: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves connected reductivity of an actual group scheme. -/
theorem connectedReductiveFieldExtensionStatement :
    ConnectedReductiveFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  refine ⟨?_, ?_, G.connectedSpace_baseChange_of_smooth_affine _, ?_⟩
  · change Smooth (pullback.snd G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  · change IsAffineHom (pullback.snd G.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    infer_instance
  · let Gbar := (GroupScheme.baseChange (toAlgebraicClosure k)).obj G
    let : Smooth Gbar.X.hom := by
      change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
      infer_instance
    let : IsAffineHom Gbar.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
      infer_instance
    let : ConnectedSpace Gbar.X.left := hG.connectedSpace_toAlgebraicClosure
    let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
      (algebraicClosureEmbedding k K).toRingHom.toAlgebra
    have hrad := algebraicallyClosedRadicalFieldExtensionStatement
      (AlgebraicClosure k) (AlgebraicClosure K) Gbar
      inferInstance inferInstance inferInstance hG.hasTrivialGeometricUnipotentRadical
    exact HasTrivialUnipotentRadical.of_iso
      ((algebraicClosureBaseChangeIso k K).app G).symm hrad

end Langlands.GroupScheme
