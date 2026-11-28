import Langlands.Global.LocalWavePacketMainTermChamberStatement
import Langlands.Global.LocalWavePacketMainTermFamilyStatement

/-! # Reduction of the limit of the integrated main terms in Lapid's §8

Lapid 2011, §8, p.328 derives the limit of the integral (18) of the main terms of formula (2)
from two inputs and Lemma 8 (`Langlands.GMFamily.OrthogonalSetLimitStatement`):

* the parametrization of the chambers of `𝔞_P` by the Weyl sets `Ω(P, S)`
  (`StandardChamberParametrizationStatement`), which writes the main term as a sum over
  `𝓟(M)` of the `(G, M)`-family `c_Q(T; Λ) = e^{Λ(Y_Q)}` times a second family, divided
  chamber by chamber by `θ_Q(Λ)`. For `t' = t s` the spectral difference is
  `Λ = λ − sλ'`, since `tλ + t' conj(λ') = t(λ − sλ')` on the imaginary axis.
* the `(G, M)`-family property of the inner products in the main term and their value at the
  origin (`WavePacketMainTermFamilyStatement`).

`WavePacketMainTermLimitReductionStatement` is the implication from these two statements to
`WavePacketMainTermLimitStatement`. This file states the implication and does not prove it. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global

/-- **Reduction of Lapid's §8 limit (p.328).** The parametrization of the chambers of `𝔞_P`
by the Weyl sets (`StandardChamberParametrizationStatement`) and the `(G, M)`-family property of
the inner products of the main term (`WavePacketMainTermFamilyStatement`) imply the limit of the
integrated main terms, `WavePacketMainTermLimitStatement`. -/
def WavePacketMainTermLimitReductionStatement : Prop :=
  StandardChamberParametrizationStatement → WavePacketMainTermFamilyStatement →
    WavePacketMainTermLimitStatement

end Langlands.Global
