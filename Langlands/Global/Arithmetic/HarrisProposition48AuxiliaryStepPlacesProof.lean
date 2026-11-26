import Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement
import Langlands.Global.Arithmetic.HarrisUniquePlace
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof

/-! # The auxiliary places of a CM step field in Harris's Proposition 4.8 -/

universe uF

namespace Langlands.Global.Harris

open AdelicFunctoriality

/-- A CM step field `E ⊆ D ⊆ L` has exactly one place above the auxiliary base
place and exactly one above its conjugate, and complex conjugation of `D` carries
the first to the second. -/
theorem proposition48AuxiliaryStepPlaces :
    Proposition48AuxiliaryStepPlacesStatement.{uF} := by
  intro Q D _ hQ w
  obtain ⟨-, -, -, -, -, -, hu, huc, -⟩ := hQ
  refine ⟨⟨conjPlace D w.val, HarrisDatum.conjPlace_liesOver Q.Ps.v w.val⟩, rfl,
    fun w' ↦ ?_, fun w' ↦ ?_⟩
  · exact (finitePlacesAbove_subsingleton (L := Q.L) Q.Ps.v hu).elim w' w
  · exact (finitePlacesAbove_subsingleton (L := Q.L) (conjPlace Q.E Q.Ps.v) huc).elim w' _

end Langlands.Global.Harris
