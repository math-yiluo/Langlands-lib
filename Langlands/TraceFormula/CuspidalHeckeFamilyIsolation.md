# Isolating the Hecke family of a cuspidal class by its constituent count

This module states and proves the Hecke-level isolation step that Clozel–Rajan, *Solvable base change*, arXiv:1806.02513v1, §7.3 (PDF p. 26), use to close the proof of their Theorem 1. There they say that the cuspidal representations in the discrete twisted trace have families of Hecke eigenvalues, away from a finite set of primes, "linearly independent, and independent from those of other representations". They also say that the cuspidal sum gives characters of the Hecke algebra "linearly independent from all others, associated to induced representations". This file proves the part of that remark that concerns a single Hecke family: under the constituent recovery of Jacquet–Shalika, *On Euler products and the classification of automorphic forms II*, Theorem 4.4 (printed p. 809, PDF p. 34), the unramified Hecke family of a cuspidal class is not carried by any attached cuspidal support whose number of constituents, counted with multiplicity, is not one.

Every result after the first two lemmas assumes the Library's proposition `CuspidalEulerConstituentRecoveryAt.{uF, uV} F`. This module does not prove it. It is the body, at one number field, of the published target `CuspidalEulerConstituentRecoveryStatement`, the Euler-polynomial form of the numerical step of JS81 II Theorem 4.4. `recoveryAt_of_statement` and `recoveryAt_of_TCStatement` derive it from the general target and from the totally complex target `CuspidalEulerConstituentRecoveryTCStatement`, so a later proof of either target supplies the hypothesis.

Throughout, `F` is a number field with the Library's assumption `CompactSpace (AdeleQuotient F)`. Cuspidal entries are `PositiveRankCuspidalClass F`, full operator-equivalence classes of actual irreducible cuspidal realizations on `GL_(r+1)` over the adeles of `F`, of any positive rank. A numerical spectral system is attached to a class through `PositiveRankCuspidalClass.HasSpectralSystem.{uF, uV}`, a genuine spectral presentation inside an actual representative. "Same Euler polynomials" is `SpectralSystem.SameEulerPolynomials`: the normalized local Euler polynomials agree at all finite places outside a finite set. Ranks may differ.

## The definition

`CarriesCuspidalHeckeFamily.{uF, uV} c₀ s` says that the spectral system `s`, of any rank `n`, has the same Euler polynomials off a finite set as some system `s₀` attached to the cuspidal class `c₀`. It is an existential over the attached system. No canonical Satake system of `c₀` is chosen, and no arbitrary numerical system is identified with an automorphic object. `carriesCuspidalHeckeFamily_of_hasSpectralSystem` says that an attached system carries the family of its own class. `CarriesCuspidalHeckeFamily.of_sameEulerPolynomials` says that the property depends only on Euler polynomials off a finite set.

## Recovery with arbitrary finite index types

`sameEulerPolynomials_finiteSum_reindex` says that reindexing a finite family of systems along an equivalence does not change the Euler polynomials of its `SpectralSystem.finiteSum`. The proof uses `SpectralSystem.finiteSum_eulerPolynomial` on both sides and `Fintype.prod_equiv`. It needs no recovery hypothesis.

`exists_equiv_of_sameEulerPolynomials` extends the recovery hypothesis from families indexed by `Fin p` and `Fin q` to families indexed by arbitrary finite types `J` and `K`. If the finite sums of the attached systems have the same Euler polynomials, there is an equivalence `e : J ≃ K` with `c j = d (e j)` for all `j`. The proof transports both families along `Fintype.equivFin` and applies the hypothesis. It composes the resulting bijection with the two enumerations. Multiplicities are kept, since neither family needs to be injective. This is the form needed for the block families `Fin d × Fin m` of `CyclicTwistedHeckeBlockTransfer`.

## Isolation results

All of these assume `hrec : CuspidalEulerConstituentRecoveryAt.{uF, uV} F`. Each one has two forms: one takes an attached system `s₀` of `c₀` (hypothesis `h₀`) and concludes about `s₀.SameEulerPolynomials s`, and the other concludes about `CarriesCuspidalHeckeFamily.{uF, uV} c₀ s`. In each pair the `CarriesCuspidalHeckeFamily` form unpacks the existential and applies the first form.

- `eq_of_sameEulerPolynomials` and `eq_of_carriesCuspidalHeckeFamily`: two cuspidal classes with attached systems that have the same Euler polynomials off a finite set are equal. This is strong multiplicity one at the level of full cuspidal classes. The proof is the one-term case `Fin 1` of recovery, using `IsobaricData.sameEulerPolynomials_finiteSum_one`.
- `not_sameEulerPolynomials_of_card_ne_one` and `not_carriesCuspidalHeckeFamily_of_card_ne_one`: let `d : K → PositiveRankCuspidalClass F` be a finite family, repetitions allowed, with attached systems `t`. If a system `s` has the Euler polynomials of their finite sum and `Fintype.card K ≠ 1`, then `s` does not carry the Hecke family of any cuspidal class. Recovery against the one-term family `Fin 1` would give an equivalence `Fin 1 ≃ K`.
- `not_sameEulerPolynomials_of_blocks` and `not_carriesCuspidalHeckeFamily_of_blocks`: the special case `K = Fin d × Fin m` with `1 < d`. The cardinality `d * m` is not one, because `d * m = 1` forces `d = 1`.
- `eq_ofCuspidal_of_sameEulerPolynomials` and `eq_ofCuspidal_of_carriesCuspidalHeckeFamily`: for an isobaric datum `D` (a finite multiset of positive-rank cuspidal classes) with an attached system `s` in the sense of `IsobaricData.HasSpectralSystem`, if `s` carries the Hecke family of `c₀` then `D = IsobaricData.ofCuspidal c₀`. The proof unpacks the enumeration `σ : Fin k → PositiveRankCuspidalClass F` of `D` and gets `k = 1` and `σ 0 = c₀` from recovery. It then evaluates the multiset `Finset.univ.val.map σ`.
- `not_sameEulerPolynomials_of_isobaric_card_ne_one` and `not_carriesCuspidalHeckeFamily_of_isobaric_card_ne_one`: an isobaric datum with `Multiset.card D ≠ 1` has no attached system carrying the Hecke family of a cuspidal class.

## How the results are used

In Clozel–Rajan §7.3, the representations that compete with a cuspidal `Π` are of three kinds: residual discrete representations, terms induced from proper Levi subgroups, and the transferred contributions of the endoscopic group `H`. Each of them has a cuspidal support (an isobaric datum or block family) with more than one constituent. For the endoscopic contributions, `CyclicTwistedHeckeBlockTransfer.exists_twistedBlockSystem_support` gives the transferred Hecke data of a supported system as the finite sum of systems attached to an explicit family indexed by `Fin d × Fin m`. With `1 < d` (in particular for prime `d`), `not_carriesCuspidalHeckeFamily_of_blocks` shows that this Hecke data never carries the Hecke family of a cuspidal class. For residual and proper-Levi terms, `not_carriesCuspidalHeckeFamily_of_isobaric_card_ne_one` gives the same conclusion once their cuspidal supports and attachments are supplied.

## Scope

This file works only at the level of unramified Hecke families. It does not prove or assume any of the following:

- `CuspidalEulerConstituentRecoveryAt` or the Jacquet–Shalika theorems; recovery is a hypothesis;
- that a given residual, proper-Levi or endoscopic term of the discrete trace formula has a cuspidal support with attached systems, or that this support has more than one constituent (for residual Speh-type and induced terms these are Mœglin–Waldspurger and Langlands results that later units must supply);
- multiplicity one in the discrete spectrum, or linear independence of the Hecke characters of infinitely many representations;
- any trace identity, or any separation of a trace identity into Hecke eigencomponents.

Distinct Hecke families alone do not separate an identity of infinite spectral sums. The intended route is the localization at a fixed Hecke eigencharacter outside a finite set of places, as in Mœglin–Waldspurger, *Stabilisation de la formule des traces tordue*, vol. II, X.5.1 and X.5.9. Inside one localized component, this file identifies which terms can carry the Hecke family of a given cuspidal class.
