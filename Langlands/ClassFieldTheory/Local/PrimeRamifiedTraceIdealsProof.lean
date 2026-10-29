import Langlands.ClassFieldTheory.Local.PrimeRamifiedTraceIdealsStatement
import Langlands.ClassFieldTheory.Local.PrimeRamifiedDifferentProof
import Langlands.LocalField.DVRTraceIdealsProof
import Langlands.ClassFieldTheory.Local.NYLL.RelativeIntegerStructureProof
import Langlands.LocalField.RelativeIdealPowers

/-! Exact trace images for the supplied prime ramification break. -/

namespace Langlands.LocalClassField

universe u v

open PadicField.TopologicalData

/-- The exact trace image of every nonnegative ideal power at the supplied
prime ramification break, for the actual canonical integer rings. -/
theorem primeRamifiedTraceIdeals : PrimeRamifiedTraceIdeals.{u,v} := by
  intro p hp F L hFL hbase hfinite hgalois
  dsimp only
  intro hell hram t hbreak n y
  let TF := F.canonicalTopologicalData
  let TL := L.canonicalTopologicalData
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TL.topology
  let := TL.valuativeRel
  let := TL.localField
  let := relativeIntegerAlgebra TF TL
  let := relativeIntegerFieldAlgebra (E := L) TF
  let := relativeIntegerFieldTower (E := L) TF
  let := relativeIntegerTower TF TL
  obtain ⟨hclosure, hmodule⟩ := NYLL.relativeIntegerStructure p F L TF TL
  let := hclosure
  let := hmodule
  have hmap := map_maximalIdeal_algebraMap_of_ramificationIndex_eq_mul
    TF TL (Module.finrank F.Carrier L.Carrier) hram
  have hdiff := primeRamifiedDifferent p F L hell hram t hbreak
  exact LocalField.dvrTraceIdeals TF.Integers TL.Integers F.Carrier L.Carrier
    (Module.finrank F.Carrier L.Carrier)
    ((t + 1) * (Module.finrank F.Carrier L.Carrier - 1))
    hell.pos hmap hdiff n y

end Langlands.LocalClassField
