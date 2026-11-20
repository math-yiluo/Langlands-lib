import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.OperatorArithmeticTransportClasses

/-! # Spectra of arithmetic pullbacks of cuspidal classes -/

noncomputable section

universe uI uJ uK uL uV

set_option autoImplicit false

namespace Langlands.Unramified.SpectralSystem

/-- Transport the exceptional set and eigenvalues along an equivalence of places. -/
def reindex {I : Type uI} {J : Type uJ} {n : ℕ}
    (s : SpectralSystem I n) (e : I ≃ J) : SpectralSystem J n where
  exceptional := s.exceptional.map e.toEmbedding
  eigenvalues v hv := s.eigenvalues (e.symm v) fun h =>
    hv (Finset.mem_map.mpr ⟨e.symm v, h, e.apply_symm_apply v⟩)

end Langlands.Unramified.SpectralSystem

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open Langlands.Automorphic.CuspidalOperatorRealization

/-- Arithmetic pullback of an actual cuspidal class carries its attached
finite-place spectrum along the equivalence of places, in the same factor universe. -/
def CuspidalSpectralArithmeticComapStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (r : ℕ) (c : IsoClass L r)
    (s : SpectralSystem (FinitePlace L) (r + 1)),
    IsoClass.HasSpectralSystem.{uL, uV} c s →
    IsoClass.HasSpectralSystem.{uK, uV} (c.arithmeticComap e)
      (s.reindex (finitePlaceEquiv e))

end Langlands.Automorphic.Unramified
