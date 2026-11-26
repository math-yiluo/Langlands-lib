# Uniqueness of isobaric weak base change over arbitrary number fields

`Langlands.Automorphic.Unramified.isobaricWeakBaseChangeUniqueness` proves
`IsobaricWeakBaseChangeUniquenessStatement` with its four universe parameters
`uF`, `uE`, `uV` and `uW` and its published hypotheses. The premise is Euler
constituent recovery, `CuspidalEulerConstituentRecoveryStatement.{uE, uW}`, over
upper number fields in universe `uE`. The extension `E/F` is an arbitrary
extension of number fields with compact adelic quotients. It need not be Galois
or of prime degree, either field may have real places, and the isobaric data
need not be unitary. The conclusion is equality of the upper data as multisets
of cuspidal classes, so multiplicities are recovered as well.

## The proof

The module proves two theorems in `Langlands.Automorphic.IsobaricData` and then
applies the second one.

`eq_of_attached_sameEulerPolynomials_of_eulerConstituentRecovery` states that,
given Euler constituent recovery over `F`, two isobaric data over `F` are equal
when spectral systems attached to them have the same Euler polynomials at all
but finitely many finite places. Unfold the two attachments into enumerations
`c : Fin p → PositiveRankCuspidalClass F` and `d : Fin q → PositiveRankCuspidalClass F`
of the constituents. Each enumeration carries attached constituent systems, and
the finite sum of those systems has the same Euler polynomials as the given
system outside a finite set. Chaining these agreements with the hypothesis
compares the two finite sums, and recovery gives an equivalence
`e : Fin p ≃ Fin q` with `c i = d (e i)`. The two data are the multisets of
values of `c` and `d`, and mapping along an equivalence does not change such a
multiset.

`IsWeakBaseChangeOf.unique_of_eulerConstituentRecovery` states that recovery over
`E` makes the upper datum of an isobaric weak base change unique. The two weak
base change relations supply lower systems `s` and `s'` attached to `DF`, upper
systems `t` and `t'` attached to `DE` and `DE'`, and arithmetic weak base change
relations over `s` and `s'` for the rank transports of `t` and `t'`. The two
lower attachments may come from different presentations.
`HasSpectralSystem.sameEulerPolynomials` shows that `s'` and `s` have the same
Euler polynomials outside a finite set, and
`IsArithmeticWeakBaseChangeOf.of_sameEulerPolynomials` then puts the second
relation over `s`. Now both relations are over `s`. Each holds on a cofinite set
of places of `F`. The map from a finite place of `E` to the place of `F` below
it pulls cofinite sets back to cofinite sets (`tendsto_under_cofinite`). At an
upper place `w` of the intersection of the pulled-back sets, both upper spectra
equal the power of the lower spectrum at the place below `w`, with exponent the
residue degree of `w`. So the two upper systems have the same Euler polynomials
at `w`. Rank transport does not change Euler polynomials. The first theorem,
applied over `E` with the supplied recovery, gives `DE = DE'`.

The totally complex counterpart is
`IsobaricData.IsWeakBaseChangeOf.unique_of_eulerConstituentRecoveryTC` in the
module `Langlands.Automorphic.Unramified.IsobaricWeakBaseChangeUniqueness`. The
argument here is the same, and the totally complex hypothesis enters there only
through the recovery premise.

## Source

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), `arthur-clozel-1989-base-change`, SHA-256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
Chapter III, relation (1.1) and Definition 1.1, printed p. 199 (PDF p. 213),
define weak base change by the residue-degree power of the Hecke classes at
almost all places. The Jacquet–Shalika consequence (2.4), printed p. 200
(PDF p. 214), recovers the cuspidal data from the Hecke classes at almost all
places. Theorem III.4.2(c), printed p. 202 (PDF p. 216), asserts uniqueness,
and its proof, printed p. 206 (PDF p. 220), derives it from (2.4) together with
the irreducibility of unitary induction. The Library's formulation compares
multisets of cuspidal classes directly, and the premise
`CuspidalEulerConstituentRecoveryStatement` plays the role of (2.4).
