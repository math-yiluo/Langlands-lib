# Construct positive decomposition from central character detection

Author: Worker 112.

This internal construction takes the proposition
`Langlands.GroupScheme.CentralSplitTorusCharacterStatement.{u}` as an
explicit input. It does not prove that proposition. The input says that
every nonzero rational character of a connected reductive group over any
field is nonzero on an actual central split subtorus.

Fix a number field `F`, a connected reductive group scheme `G/F` with
the explicit affine interface, and any actual
split component `i : T.toGrp → G`. The definition
`splitComponentNormOneDecomposition` constructs a continuous group
equivalence from
`intrinsicSubgroup F T × normOneSubgroup F G` to the actual adelic group
of `G`. It has value `positivePointMap F G T i a * n` on every `(a,n)`.
The source carries the ordinary direct product law.

## Implemented construction

The imported
`characterRestrict_injective_of_centralSplitTorusCharacter` applies the
detection input and factorization of every central split torus through
the chosen split component to prove restriction injectivity.
`characterRestrictionFiniteIndexStatement` supplies finite index from
its published proof, without another hypothesis.

The split-component predicate supplies an isomorphism of `T.toGrp`
with a finite-rank split torus and supplies actual centrality of `i`.
Use classical choice for the finite indexing type, its finiteness witness
and splitting isomorphism, choose a finite enumeration, and apply
the existing `normOneDecompositionMulEquiv` to this splitting,
injectivity, finite index and centrality. That existing construction
uses the actual character logarithm to recover the positive factor,
then removes its image from the original point to obtain the norm-one
factor. Its continuity uses the affine adelic group topology.

`splitComponentNormOneDecomposition_apply` is definitional equality:
the forward multiplication map is independent of the chosen splitting.
`hasPositiveNormOneDecomposition_of_centralSplitTorusCharacter` records
this equivalence and formula in the previously defined predicate.
Finally,
`adelicPositiveDecomposition_of_centralSplitTorusCharacter` obtains a
split component from the published `splitComponentStatement` and applies
the construction. Its complete result is the implication from the
named detection proposition to
`AdelicPositiveDecompositionStatement.{u}`.

All assertions are derived from those imported definitions and proofs;
no external structural theorem is added. The result retains arbitrary
universe `u`, all number fields, nonsplit and anisotropic cases, and
empty split rank. It works for every supplied split component; only the
last existence consequence chooses one.

The detection proposition remains an explicit open premise. This
construction therefore does not prove the unconditional decomposition
target. It also does not identify the positive image with the greatest
`ℚ`-split centre after Weil restriction, or assert any quotient or
measure comparison, Haar invariance, finite volume or reduction theory.
