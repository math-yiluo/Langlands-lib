import Langlands.Global.RankinSelberg.WhittakerIntegrals

/-! # The modulus of right multiplication on adelic rectangular matrices -/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance rectangleModulusMeasurableSpace (F : Type u) [Field F] [NumberField F]
    (k m : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) :=
  borel _

/-- Right multiplication `x ↦ x g` by `g ∈ GL_m(𝔸)` on the adelic rectangular matrices
`M_{k×m}(𝔸)` multiplies the rectangular Haar measure by `|det g|_𝔸^k`. In the pushforward
convention: the image of `rectangleMeasure F k m` under `x ↦ x g` is `|det g|_𝔸^{-k}` times
`rectangleMeasure F k m`. -/
def RectangleMeasureModulusStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (k m : ℕ)
    (g : Points F m),
    Measure.map (fun x : Matrix (Fin k) (Fin m) (Adeles F) =>
        x * ((GeneralLinearGroupPoints.adelicEquiv F m g :
          Matrix.GeneralLinearGroup (Fin m) (Adeles F)) : Matrix (Fin m) (Fin m) (Adeles F)))
      (rectangleMeasure F k m) =
      ENNReal.ofReal ((detNorm F m g ^ k)⁻¹) • rectangleMeasure F k m

end Langlands.Global.RankinSelbergGlobal
