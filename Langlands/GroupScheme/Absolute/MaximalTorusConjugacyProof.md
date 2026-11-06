# Conjugacy of maximal tori over algebraically closed fields

Workers 1354 and 1357.

`Langlands.GroupScheme.maximalTorusConjugacy` proves the unchanged
`Langlands.GroupScheme.MaximalTorusConjugacyStatement.{u}`. Let `k : Type u`
be any algebraically closed field and `G` a smooth affine group scheme over
`Spec k` with connected underlying space. For every two commutative group
schemes `T`, `T'` and actual maximal torus embeddings `j : T.toGrp ⟶ G`,
`j' : T'.toGrp ⟶ G`, the theorem gives a rational point `g` of `G` and an
isomorphism `φ : T ≅ T'` in the commutative group-scheme category such that

```text
j ≫ (G.innerIso g).hom = CommGroupScheme.groupHom φ.hom ≫ j'.
```

The theorem retains arbitrary universe and characteristic and the full smooth
affine connected scope. It has no additional structural premise.

## Implemented proof and inputs

The proof applies the published
`maximalTorusConjugacyStatement_of_borelConjugacy` from
`Absolute.BorelMaximalTorusReduction` and supplies both of its inputs with
published proofs.

The first input is `borelConjugacy`, imported from
`Absolute.BorelConjugacyProof`. It proves the exact Borel existence and
conjugacy proposition for the same general ambient groups. Its proof uses a
proper quotient by a Borel, the actual descended quotient action, the general
solvable fixed-point theorem and the fixed-point-to-conjugacy adapter.

The second input is `solvableMaximalTorusConjugacy`, imported from
`Rational.SolvableMaximalTorusConjugacyProof`. That theorem proves rational
conjugacy of maximal tori over every field in every smooth connected affine
solvable group. The lambda in this file simply specializes it to the
algebraically closed fields and solvable groups required by the reduction.
Its published proof constructs the geometric torus quotient using the actual
triangular diagonal kernel geometry and closed-subgroup unipotence proofs,
then applies the arbitrary-field retained-quotient and torus-generated-envelope
assembly. Those constructions and their source comparisons are documented in
that imported proof pair.

The reduction discharges containment through the unconditional
`maximalToriLieInBorels`: each given torus is smooth, connected and solvable,
and its closed embedding factors through an actual Borel. It conjugates the
two resulting Borel embeddings by `borelConjugacy`, transports one torus to
the other Borel, and restricts ambient maximality through the closed
embeddings. The specialized solvable theorem then conjugates the two maximal
tori inside that common Borel. The published overgroup conjugacy constructor
composes the actual rational points and source isomorphisms and returns the
ambient morphism equation.

Finally, `subgroupConjugate_iff_exists_commGroupSchemeIso`, used inside the
reduction, lifts the source isomorphism from group schemes to commutative
group schemes by wrapping its two maps and inverse identities. It retains the
same rational conjugator and equation. The supplied embeddings are preserved
throughout the construction. The published target pair and its imports are
unchanged.

## Original source and provenance

The original source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
Theorem 17.10 is on printed p.354 / one-based PDF p.370, with its proof on
printed p.355 / PDF p.371. The standing connected-group and algebraically
closed-field assumptions are at the start of Section 17b on printed p.353 /
PDF p.369.

The source places each torus in a Borel, conjugates the Borels using Theorem
17.9, and applies solvable-group conjugacy inside the common Borel.
Theorem 16.33(d), printed pp.335–336 / PDF pp.351–352, supplies that solvable
input in Milne's argument. These original passages were read, along with the
complete registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.
The errata contain no correction to these results.

This file is an internal composition of the named published proofs. Its outer
argument follows Milne's proof, while the imported Borel and solvable proofs
use the implemented quotient and fixed-point routes described above. No
unproved Borel, solvable conjugacy, maximal-torus existence or base-change
proposition is retained as an input.
