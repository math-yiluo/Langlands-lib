import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly
import Langlands.Representation.Classification.ProductLeviTemperedExponentNecessityProof

/-!
# Tempered scalar-character layers of the opposite Jacquet module

The conditional assembly `glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity`
applied to the published necessity theorem `glProductLeviTemperedExponentNecessity`.
-/

namespace Langlands

universe uF uV uW

/-- For an irreducible analytically tempered GL_n representation, every subquotient of its
opposite normalized Jacquet representation with an exact unitary scalar central character is
analytically tempered modulo the full Levi centre, for every Borel Haar measure. -/
theorem glTemperedOppositeJacquetScalarLayer :
    GLTemperedOppositeJacquetScalarLayerStatement.{uF, uV, uW} :=
  glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity
    glProductLeviTemperedExponentNecessity.{uF, uV}

end Langlands
