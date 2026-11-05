import Langlands.ClassFieldTheory.Local.Norms
import Langlands.Galois.Local.SeparableInertiaDefinitions

/-! # Norm surjectivity on units over the separable inertia fixed field -/

namespace Langlands.ClassFieldTheory.Local

open Langlands.LocalGalois.Separable

universe u

/-- For every nonarchimedean local field `F` (of either characteristic), every finite
extension `E` of the separable inertia fixed field `U ⊆ F^sep`, and every finite extension
`L` of `E` inside `F^sep`, the norm `L → E` maps the units of `L` (elements of absolute
value one for the spectral valuation of `F^sep`) onto the units of `E`. -/
def SeparableInertiaUnitNormSurjectivity : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (E : IntermediateField (inertiaFixedField F) (SeparableClosure F))
    [FiniteDimensional (inertiaFixedField F) E]
    (L : IntermediateField E (SeparableClosure F)) [FiniteDimensional E L]
    (u : Eˣ), sepClosureValuation F ((u : E) : SeparableClosure F) = 1 →
      ∃ x : Lˣ, sepClosureValuation F ((x : L) : SeparableClosure F) = 1 ∧
        Langlands.LocalClassField.normUnits E L x = u

end Langlands.ClassFieldTheory.Local
