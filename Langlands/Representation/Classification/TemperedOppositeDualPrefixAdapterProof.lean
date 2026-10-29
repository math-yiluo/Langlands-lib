import Langlands.Representation.Classification.TemperedOppositeDualPrefixAdapterStatement
import Langlands.Representation.Classification.TemperedOppositeJacquetScalarLayerAssembly

/-!
# Necessary upper bounds imply opposite full-dual prefix bounds

The upper necessity theorem remains the sole premise of this adapter.
The conversion uses the published primal spectrum, one-block transport,
normalized block reversal and scalar prefix test constructions.
-/

namespace Langlands

open GeneralLinear

/-- The exact upper product-Levi necessity proposition implies the nonpositive
scalar real-part prefixes of every opposite full-dual exponent of an
irreducible analytically tempered GL source. -/
theorem glTemperedOppositeDualPrefixAdapter.{uF, uV} :
    GLTemperedOppositeDualPrefixAdapterStatement.{uF, uV} := by
  intro hnec p _ F T
  let := T.topology
  intro n hn B A hirr htemp χ s hχ hs
  have hadm : IsAdmissible A.ρ := htemp.isAdmissible
  have hgen := ScalarLayer.isGeneralizedEigencharacter_of_isDualJacquetExponent
    T B A hirr hadm hχ
  have hexp := ScalarLayer.isJacquetExponent_reverse T B A hχ.1 hgen
  have hup := ScalarLayer.temperedUpperExponentBound_of_productLeviNecessity hnec
  have hbound : ∀ a : Fin B.length → F.Carrierˣ,
      Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) →
      ‖(χ a : ℂ)‖ ≤ 1 := by
    intro a ha
    have h := hup p F T n hn A A.ρ hirr htemp B.reverse _ hexp
      (a ∘ Fin.rev) (fun i j hij => ha (Fin.rev_le_rev.mpr hij))
    have hrev : (a ∘ Fin.rev) ∘ Fin.rev = a := by
      funext k
      simp
    change ‖(χ ((a ∘ Fin.rev) ∘ Fin.rev) : ℂ)‖ ≤ 1 at h
    rwa [hrev] at h
  exact ScalarLayer.prefix_nonpos_of_antitone_bound T hs hbound

end Langlands
