import Langlands.Automorphic.OperatorArithmeticTransportClasses
import Langlands.Automorphic.CuspidalSpectralPresentation

/-!
# Arithmetic pullback carries attached spectral systems

For an isomorphism of number fields `e : K ≃+* L`, the arithmetic pullback of a
cuspidal class over `L` to `K` has, at almost every finite place `v` of `K`, the
unramified Euler polynomial of the original class at the place `e(v)` of `L`.
Proposition definition only.
-/

noncomputable section

universe uK uL uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified

/-- Transport of structure for unramified spectra along `e : K ≃+* L`. If the
spectral system `s` is attached to the cuspidal class `c` over `L`, then some
spectral system `s'` attached to the pulled-back class `c.arithmeticComap e` over
`K` has, at all but finitely many finite places `v` of `K` where both are
defined, the Euler polynomial of `s` at the corresponding place
`(finitePlaceEquiv e).symm v` of `L`. -/
def CuspidalArithmeticSpectralTransportStatement : Prop :=
  ∀ (K : Type uK) (L : Type uL) [Field K] [NumberField K] [Field L] [NumberField L]
    [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
    (e : K ≃+* L) (r : ℕ) (c : CuspidalOperatorRealization.IsoClass L r)
    (s : SpectralSystem (FinitePlace L) (r + 1)),
    CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uL, uV} c s →
      ∃ s' : SpectralSystem (FinitePlace K) (r + 1),
        CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uK, uV}
            (CuspidalOperatorRealization.IsoClass.arithmeticComap e c) s' ∧
          ∀ᶠ v in Filter.cofinite, ∀ (hv : v ∉ s'.exceptional)
            (hw : (finitePlaceEquiv e).symm v ∉ s.exceptional),
            s'.eulerPolynomial v hv = s.eulerPolynomial ((finitePlaceEquiv e).symm v) hw

end Langlands.Automorphic
