# Actual torsion cardinality from an ample pullback identity

This internal adapter applies the proved theorem
`Langlands.AlgebraicGeometry.Picard.polarizedFiniteFlatRank` to the actual
abelian specialization in `GeometricTorsionPolarizedRank`. The general
numerical rank proposition is therefore discharged by its proof, rather than
retained as an assumption.

Let `B / Spec K` be an actual bundled abelian scheme over an algebraically
closed field, with specified smooth relative dimension `g`. Let `n > 0`
be nonzero in `K`, let `L` be an actual ample line bundle on `B`, and supply
an actual module-sheaf isomorphism

```text
[n]* L ≅ L^(tensor (n*n)).
```

`multiplicationFinrank_of_amplePullback` proves that the native rank of
the actual multiplication morphism at every target point is `n^(2*g)`.
It supplies `polarizedFiniteFlatRank` to the existing specialization.
That specialization uses the actual multiplication morphism's proved
finiteness and etaleness, hence flatness, and the given smooth relative
dimension, properness and geometric connectedness. The polarization factor
is `n*n`, whose `g`-th power equals `n^(2*g)`.

`natCard_level_of_amplePullback` supplies the same proved numerical theorem
to the published actual torsion/native-rank comparison. Its conclusion
counts the existing `GroupScheme.Tate.Level` over the identity field point:
its cardinality is `n^(2*g)`. No coordinate basis, numerical rank or degree
formula is supplied as data.

The definition `torsionEquivFinOfAmplePullback` uses that cardinality and
its positivity to enumerate the actual torsion type by `Fin (n^(2*g))`.
It first uses `Nat.equivFinOfCardPos`, then transports the finite target
along the cardinality equality. This is an equivalence of types; it makes
no claim about addition or the residue-ring action.

`fieldTorsionCardinality_of_symmetricGeometry` provides the universal
field-level cardinality interface needed by the separate torsion-structure
and relative-transport reduction. It applies
`fieldTorsionCardinality_of_numericalGeometry` with the proved numerical
theorem. The two remaining premises,
`GroupScheme.FieldSymmetricAmpleExistenceStatement` and
`GroupScheme.FieldSymmetricMultiplicationPullbackStatement`, remain
explicit. They provide the actual ample bundle and its actual pullback
identity. This module does not prove either proposition or the unconditional
geometric torsion rank statement.

The provenance is an internal composition of published Lean results.
The general numerical theorem uses actual Euler polynomials, the finite-flat
native-rank coefficient comparison and tensor-power dilation, as explained
in its paired Markdown. The existing abelian specialization and actual
torsion comparison retain their original meanings and hypotheses. No new
original-source assertion or unproved numerical certificate is introduced.
Arbitrary characteristic, level one and dimension zero are preserved.
