import Langlands.Algebra.ReducedNorm
import Langlands.Global.AdelicGroupLocalPoints

/-! # Locality of reduced norms over number fields -/

universe u

namespace Langlands.CentralSimple

/-- A nonzero scalar that is a reduced norm at every completion is a reduced norm over the
number field. The tensor algebra over the original field is canonically the original algebra. -/
def NumberFieldReducedNormLocalityStatement : Prop :=
  ∀ (F A : Type u) [Field F] [NumberField F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] (a : Fˣ),
    (∀ v : Global.Place F,
      let K := Global.placeCompletion F v
      Units.map (algebraMap F K).toMonoidHom a ∈ Set.range (reducedNormUnits F A K)) →
    a ∈ Set.range (reducedNormUnits F A F)

end Langlands.CentralSimple
