import Langlands.Automorphic.Unramified.CuspidalSpectralArithmeticComapStatement
import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof

/-! # Exact spectral attachment under arithmetic pullback -/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global.AdelicFunctoriality Langlands.Unramified

/-- Pullback of an actual cuspidal realization carries the supplied spectrum
with exactly the prescribed exceptional set and eigenvalues. -/
theorem cuspidalSpectralArithmeticComap :
    CuspidalSpectralArithmeticComapStatement.{uK, uL, uV} := by
  intro K L _ _ _ _ _ _ e r c s hs
  obtain ⟨S, P, rfl, rfl⟩ := hs
  refine ⟨S.arithmeticComap e, P.arithmeticComap e, rfl, ?_⟩
  have hplaces : finitePlaceEquiv e.symm = (finitePlaceEquiv e).symm := by
    apply Equiv.ext
    intro v
    apply (finitePlaceEquiv e).injective
    rw [Equiv.apply_symm_apply, ← Equiv.trans_apply, ← finitePlaceEquiv_trans,
      RingEquiv.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]
  change P.spectralSystem.reindex (finitePlaceEquiv e.symm).symm =
    P.spectralSystem.reindex (finitePlaceEquiv e)
  rw [hplaces, Equiv.symm_symm]

end Langlands.Automorphic.Unramified
