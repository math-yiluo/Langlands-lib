# Finite prime cyclic towers and supplied isobaric chains

This is internal vocabulary for B6 in the operator plan
`operator-external-inputs-plan-2026-11-16`, Section 2.2. Its provenance is also
Section 4.8, Remark 4.2, claim (1), proof (1)–(2), and the paragraph “The remark
and the Library's statements”. The plan's descending notation
`K₀ ⊃ ⋯ ⊃ Kₛ = F` is indexed here in the opposite direction: level zero is
the bottom, and level `length` is the top.

`Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower F K` supplies
a finite increasing family of actual intermediate fields of the actual
extension `K/F`. At every adjacent pair the algebra is the inclusion
`stepMap : lower →ₐ[F] upper`; `stepAlgebra` exposes this exact algebra.
The tower requires that each such extension is Galois, its automorphism group
is cyclic, and its finite degree is prime. Number-field instances on the
intermediate fields and finiteness of the extensions come from Mathlib.
There is no assumption that the whole extension `K/F` is Galois or cyclic.

The endpoint equalities say that the bottom intermediate field is `⊥` and
the top intermediate field is `⊤`. Neither carrier is definitionally the
actual field. `bottomEquiv : bottom ≃ₐ[F] F` is the intermediate-field
equality equivalence followed by Mathlib's `botEquiv`.
`topEquiv : top ≃ₐ[F] K` similarly uses `topEquiv`.
Both are specified actual equivalences compatible with the given embedding
`F → K`.

Length zero is allowed: there is one level and no adjacent condition.
The two endpoint equivalences then identify that one carrier with both
actual fields. `PrimeCyclicBaseChangeTower.refl F` constructs this case for
the identity extension `F/F`, using the fact that its intermediate-field
lattice has only one element. It imposes no spurious prime-degree step.

`PrimeCyclicBaseChangeTower.IsobaricChain` is only a supplied dependent family
of actual `IsobaricData`, one multiset at every level. The explicit compactness
instances for the additive adele quotients are the hypotheses used by the
Library's cuspidal vocabulary. They are supplied separately from the field
tower. `IsobaricChain.IsUnitary` applies the existing `IsobaricData.IsUnitary`
at every level; it does not require an intermediate datum to be cuspidal or
supercuspidal.

`IsobaricChain.IsSuccessiveWeakBaseChange` is a separate proposition:
for every adjacent pair, the **upper** datum is
`IsobaricData.IsWeakBaseChangeOf` the **lower** datum for `stepAlgebra`.
Thus it retains exactly the existing relation's equality of ranks and
existence of attached spectral systems. In length zero this proposition
has no instances to check. Two independent families `D` and `D'` can share
the same tower and compactness instances; neither family is built into the
tower.

`IsobaricData.arithmeticComap e` maps each constituent by the already
published `PositiveRankCuspidalClass.arithmeticComap e`. For
`e : F ≃+* K` it takes data over `K` to data over `F`. Multiplicities and
ranks are preserved by multiset mapping. The two accompanying lemmas
compute the rank and the pullback of a singleton.
`IsobaricChain.StartsAt D DF` requires the bottom datum to equal the
pullback of the actual base datum `DF` along `bottomEquiv`.
`StartsAtCuspidal D c` specializes `DF` to precisely
`IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)`.
For `c : CuspidalOperatorRealization.IsoClass F r`, total rank is `r + 1`.
`IsobaricChain.terminal D` takes the last datum to the actual top field `K`
by pullback along `topEquiv.symm : K ≃ top`. Its rank lemma is the same
multiset rank calculation.

Arthur–Clozel (1989), Chapter III Definition 4.1 and Theorem 4.2(c),
printed p.202 (registered PDF page 216), motivate the use of general data
induced from unitary cuspidal constituents throughout the tower. Their
Theorem III.5.1, printed p.212 (PDF page 226), is stated in that generality.
The later B6 argument also uses the uniqueness of local lifting from
I.6.2, printed p.51 (PDF page 65), and its extension by the Langlands
classification in I.6.4, printed pp.59–60 (PDF pages 73–74).
These are provenance for the definitions and a later proof, not results
proved by this module.

In particular this module states no B6 implication, constructs no weak
base change, and proves no existence, uniqueness, transitivity or local
compatibility theorem. A supplied successive chain is not identified with
an arbitrary weak base change for the composite extension, nor with an
existential or universal chain formulation. Such comparisons require
additional mathematics.
