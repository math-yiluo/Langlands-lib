# Numerical injections compatible with cyclic base change

Let `S : CyclicPrimeStep.{uK} p` be a cyclic extension \(M/L\) of prime degree
of \(p\)-adic fields, with \(L={\tt S.base}\), \(M={\tt S.top}\), and
\(\Gamma=\operatorname{Gal}(M/L)\) given by `S.Gal`. The positive rank is
\(k+1\), represented by `k.succPNat` in Lean. The universes `uK`, `uW`, and
`uV` index fields, Weil representation carriers, and supercuspidal
representation carriers independently.

## Definitions in `Langlands.Henniart.Numerical`

1. `IsRestrictionDecomposition S σ m` says that the restriction to \(W_M\)
   of the irreducible Weil class \(\sigma\) over \(L\) is isomorphic to the
   direct sum of the irreducible classes in \(m\). It uses
   `Weil.Local.extensionRestrictClass` along `S.embedding`. The predicate
   requires a list enumerating \(m\) and compares genuine isomorphism classes
   using `FiniteRepresentation.directSumClass` over the finite type of list
   positions. Each occurrence contributes one summand and carries its own
   positive rank.

2. `weilConjugate S w` is the bijection on rank-\(k+1\) irreducible Weil
   classes over \(M\) given by pullback along conjugation by \(w\in W_L\).
   With \(W_M\) identified with its image in \(W_L\), the convention is
   \(\tau^w(y)=\tau(wyw^{-1})\). The bijection is
   `FiniteRepresentation.continuousIrreducibleRestrictEquiv` applied to
   `Weil.Local.finiteGaloisWeilConjugation` for `S.embedding` and `S.isGalois`.

3. `IsBaseChangeCompatible S Ch N φL φM` expresses (CI1) of the route note
   on cuspidal supports. For each rank \(k+1\le N\) and each restriction
   decomposition \(m\) of \(\sigma\), the cuspidal support
   \(\mathrm{Ch}(\varphi_L(\sigma))\) equals the multiset obtained by applying
   \(\varphi_M\) to each constituent in its own rank, with multiplicity.
   Each map in the families takes a proof that its rank is at most \(N\).
   The `Multiset.pmap` uses an explicit bound for every entry of \(m\).
   Every actual decomposition has constituent ranks at most \(k+1\) by
   dimension additivity.

4. `ReflectsGaloisInvariance S N φM` says that in each rank \(k+1\le N\), if
   the image \(\varphi_M(\tau)\) is fixed by every \(g\in\Gamma\) under
   `S.galoisConjugate`, then \(\tau\) is fixed by `weilConjugate S w` for every
   \(w\in W_L\). Equivariance (CI2) and injectivity of \(\varphi_M\) imply
   this fixedness property, which is what Lemma `lem:step` uses in the case
   of a supercuspidal base change. Quantifying over both whole groups makes
   the property independent of any choice of lifts or inverse convention.
   The argument in Remark `rem:CI2` deriving this property from (CI1) uses
   (CI1) in ranks \(d[M:L]\) for \(d\le N\), which can exceed \(N\).

5. `SurjectiveBelowRank N` says that every numerical injection at a
   positive rank \(k+1<N\) over any \(q\)-adic field, for any prime \(q\), is
   surjective. The Library's `IsNumericalInjection` requires injectivity,
   preservation of the conductor whenever the Weil Artin conductor is
   given, and compatibility with unramified twists. Requiring this
   surjectivity for every \(N\) recovers `NumericalSurjectivityStatement`,
   since every positive rank is strictly below some \(N\).

## Statement in `Langlands.Henniart`

`CompatibleNumericalInjectionsStatement.{uK, uW, uV}` is input (I4) of Option II.
It says that for every prime \(p\), every step `S`, and every bound \(N\)
with `SurjectiveBelowRank N`, there are numerical injections \(\varphi_L\)
and \(\varphi_M\) in every positive rank up to \(N\). A single map `Ch`
satisfies the weak base-change properties (W1)–(W4) via
`IsWeakCyclicBaseChange S Ch` and (CI1) via
`IsBaseChangeCompatible S Ch N φL φM`. The family over \(M\) satisfies
`ReflectsGaloisInvariance S N φM`. The statement supplies (I3) by taking
\(N=0\), where the strict lower-rank premise is vacuous.

The rank bounds are part of the types of \(\varphi_L\) and \(\varphi_M\).
This avoids requiring a choice of supercuspidal images for irreducible Weil
classes in ranks above \(N\). `Ch` is the total multiset-valued map from
`HenniartCyclicBaseChange`. The rank-bounded family types, the fixedness
implication in item 4, and the lower-rank surjectivity premise are the
formulation of Task 7376. The premise supplies the earlier surjectivity
stages of the induction used to obtain the candidate's rank-\(N\) injections.

## Provenance

The mathematical template is hypothesis (CI) of §6.5 of the operator's
*The numerical local Langlands correspondence for GL_n: counts on the two
sides and the recommended route of proof*
(`operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`,
lines 1150–1174). It gives (CI1), (CI2), sources (a) and (b), and Remark
`rem:CI2`. The descent application is Lemma `lem:step` in §6.6,
lines 1177–1196.

- Source (a) is Guy Henniart, *La conjecture de Langlands locale numérique
  pour GL(n)* (1988, `henniart-1988-numerical`). Théorème 1.9, pp. 501–502,
  states compatibility with base change for numerical injections. The
  construction is in §7. Section 7.9, pp. 528–529, records equivariance
  for the Galois action used in the descent of §6.8, pp. 520–521.
- Source (b) is Guy Henniart, *Une preuve simple des conjectures de Langlands
  pour GL(n) sur un corps p-adique* (2000, `henniart-2000-simple-proof`),
  §§3.7–3.8 and 4.1–4.4, pp. 451–453, and the Library's
  `Langlands.Henniart.CandidateExistenceStatement`. Section 4.3 uses the
  bijectivity in smaller ranks for the induction and invokes Henniart (1988)
  for surjectivity. For source (b), §6.5 of the route note gives the
  unpublished assessment that compatibility with cyclic base change should
  follow from the candidate construction.
