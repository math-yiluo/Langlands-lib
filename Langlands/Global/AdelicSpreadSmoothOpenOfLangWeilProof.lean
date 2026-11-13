import Langlands.Global.AdelicSpreadSmoothOpenOfLangWeilStatement
import Langlands.Global.AdelicSpreadSmoothOpenAssemblyProof
import Langlands.Global.AdelicLevelComponentSurjectivityProof
import Langlands.Global.AdelicSmoothLocalOpen
import Langlands.Global.AdelicModelOpenReduction
import Langlands.Global.AdelicSpreadGeometricallyConnectedProof

/-! # Conrad's Theorem 4.5 from his Lemma 4.6 -/

universe u

namespace Langlands.Global

/-- Conrad's Theorem 4.5 in both characteristics, assuming only the uniform
Lang–Weil estimate: the assembly applied to the proved premises. -/
theorem adelicSpreadSmoothOpenOfLangWeil :
    AdelicSpreadSmoothOpenOfLangWeilStatement.{u} := fun hLW =>
  ⟨curvePlaceSpreadSmoothOpenAssembly hLW adelicLevelComponentSurjectivity.1
      adelicSmoothLocalPointOpen.1 adelicModelOpenReduction.1
      adelicSpreadGeometricallyConnected.1.2.2,
    numberFieldSpreadSmoothOpenAssembly hLW adelicLevelComponentSurjectivity.2
      adelicSmoothLocalPointOpen.2 adelicModelOpenReduction.2
      adelicSpreadGeometricallyConnected.2.2.2⟩

end Langlands.Global
