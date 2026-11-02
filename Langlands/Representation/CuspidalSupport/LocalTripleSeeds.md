# Actual local repeated-factor triple seeds

This internal proof establishes the literal local moves
\[
 (A,B,B)\longrightarrow(B,A,B),\qquad
 (A,B,A)\longrightarrow(A,A,B)\ \text{or}\ (B,A,A),
\]
for supplied positive-rank supercuspidal \(A,B\) with \([A]=\nu[B]\).
It then proves `UniformRepeatedCuspidalTripleJacquetTransfer` by the
existing actual representative transport. Both the input and outputs
remain actual subquotients of the upper normalized three-block Jacquet
module of the same irreducible admissible finite-length \(E\).
The field and representation universes are independent, the carriers
are in `max uF uV`, and \(F,T\) are supplied throughout.

The main algebraic step is `rightRepeatedInjectionAlternative`. At total
rank \((d+d)+d\), it takes an actual injection
\[
 E\hookrightarrow A\times B\times C,
\]
where the supplied object \(C\) is literally \(A\) or \(B\). It produces an
actual injection into \(B\times A\times C\) or \(C\times A\times B\).
All three products here use `threeBlocksRight`.

Put \(P=A\times B\), \(R=B\times A\). The actual induction-in-stages
equivalence identifies the input induction with \(P\times C\).
If \(P\) is irreducible, the lower equal-rank irreducible product swap
gives \(P\simeq R\). The actual induced right-product injection then
embeds \(E\) into \(R\times C\), and inverse regrouping gives the first
output.

If \(P\) is reducible, the proved rank-two adjacent structure supplies its
actual nonzero proper \(S\), with actual subrepresentation \(L\) and
quotient \(Q\). Normalized right-product exactness gives
\[
 0\longrightarrow L\times C\longrightarrow P\times C
   \longrightarrow Q\times C\longrightarrow0.
\]
The proved repeated-subrepresentation product theorem makes \(L\times C\)
irreducible in both cases \(C=A,B\). The generic simple-source exact
alternative therefore identifies \(E\) with \(L\times C\), or makes its
composite into \(Q\times C\) injective.

In the quotient case, the actual rank-two Jacquet formula identifies
\(r(Q)\) with \(B\otimes A\). The lower admissibility theorem for
irreducibles and the actual cuspidal constituent/first-adjunction
construction give \(Q\hookrightarrow R\). Inducing this injection with
\(C\) yields \(E\hookrightarrow R\times C\), hence the first output.

In the other case, the lower unequal-rank literal product swap identifies
the irreducible \(L\times C\) with \(C\times L\), pulled back along the
entry-preserving rank reindex. Induce the actual inclusion \(L\hookrightarrow
P\) in the second factor to obtain an injection into \(C\times P\).
`twoBlockPairEquiv` and `uniformLeftProductEquiv` make the literal factor
families and the left grouping explicit. Their inverses, the
associativity rank pullback, and `uniformRightInductionEquiv` give the
second output \(E\hookrightarrow C\times A\times B\).

`rightInductionInjection_of_uniformOccurrence` derives the initial
injection from the actual Jacquet subquotient, using the already proved
cuspidal constituent quotient theorem and first adjunction. It then uses
the explicit associativity rank pullback. The inverse transport and
`uniformTripleOccurrence_of_rightInductionInjection` recover the actual
Jacquet subquotient over the original rank \(d+(d+d)\).

For \(C=B\), both injection alternatives have the same ordered output
\(B,A,B\). For \(C=A\), they give \(B,A,A\) and \(A,A,B\), respectively.
This proves `repeatedTripleSeedTransfer`. Actual isomorphisms supplied by
equality of supercuspidal classes replace any repeated representative;
`uniformRepeatedTripleTransfer_of_seed` therefore proves the full
uniform local conjunction as `uniformRepeatedCuspidalTripleJacquetTransfer`.
The finite-length hypothesis is retained by the proposition; the
injection argument itself only needs irreducibility and admissibility.

The provenance is internal assembly of the actual local product results,
exactness, induction in stages and adjunction already named. No
irreducibility or triple transfer remains as a theorem-valued premise.
Case splitting on \(P\)'s irreducibility avoids invoking the separate
analytic adjacent-product reducibility conclusion. This module proves
the local uniform result; the ambient extraction and return are supplied
by `TripleTransferReduction`, as used in the final conjunction proof.
