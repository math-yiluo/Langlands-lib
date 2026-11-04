import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionStatement
import Langlands.GroupScheme.Absolute.ParabolicGeometricWitnessTransport
import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.AlgebraicClosureBaseChange
import Langlands.GroupScheme.GeometricConnectedness

/-! # Parabolic subgroups under arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves actual parabolic subgroup inclusions
in connected reductive group schemes. -/
theorem parabolicFieldExtensionStatement : ParabolicFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG P i hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  refine hi.baseChange_of_geometricBorel
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (algebraicClosureBaseMap k K) (algebraicClosureBaseChangeIso k K) ?_
  intro B j hj
  have hAffine : IsAffineHom
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  have hSmooth : Smooth
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  exact borelAlgClosedFieldExtensionStatement
    (AlgebraicClosure k) (AlgebraicClosure K)
    ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)
    hAffine hSmooth hG.connectedSpace_toAlgebraicClosure B j hj

end Langlands.GroupScheme
