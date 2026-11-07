import Langlands.Automorphic.CuspidalUnitaryLocalUnitarityStatement
import Langlands.Automorphic.CuspidalSpectralUnitaryForm
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # Actual local unitarity of cuspidal presentations: proof -/

noncomputable section
universe uF uQ
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global MeasureTheory

/-- Every irreducible admissible actual local component of every spectral presentation of a
cuspidal realization with unitary central character is unitarizable. -/
theorem cuspidalUnitaryLocalUnitarity : CuspidalUnitaryLocalUnitarityStatement.{uF, uQ} := by
  intro F _ _ _ r T hT P v hI hA
  obtain ⟨χ, hχ, hTχ⟩ := hT
  let : MeasurableSpace (AdelicGL F (r + 1)) := borel _
  have : BorelSpace (AdelicGL F (r + 1)) := ⟨rfl⟩
  obtain ⟨t, ht, hcover, hfinite⟩ :=
    T.realization.exists_band_cover T.cuspidal (lo := 1) (hi := 2) one_pos
  exact ⟨P.padicUnitaryFormOfCover χ hχ hTχ t ht (fun x hx => hcover x hx.1 hx.2)
    (fun f => hfinite _ f) v hI hA⟩

end Langlands.Automorphic
