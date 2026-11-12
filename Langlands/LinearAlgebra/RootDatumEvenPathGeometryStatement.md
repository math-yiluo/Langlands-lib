# Stable even-path geometry for pairing-compatible simple-root actions

Provenance: internal. This is the combinatorial existence prerequisite extracted
from the even-chain Galois-data proof. Its proposed proof uses the published
simple-root orbit dichotomy and `RootDatumReversedPath.exists_isReversedPath`,
finite selection of distinct path components, and orbit enumeration sorted by
distance from the middle. This module states that prerequisite and does not
prove it or assert any merged-root existence result.

`Langlands.LinearAlgebra.EvenPathOrbitGeometryStatement` quantifies over a finite
root index type in an arbitrary universe `u`, arbitrary additive character and
cocharacter groups in universes `v,w`, a root datum and a base, and an arbitrary
group `Γ : Type z` acting on its simple roots. Its sole action hypothesis is
`RootDatumOrbitPairs.IsPairingCompatible b ρ`: each group element extends to a
pairing-preserving permutation of the full root index type.

The conclusion supplies a finite path index type `J : Type u`, disjoint even
path components `C`, a length-preserving action on these paths which carries
ordered vertices forward or reversed, and a middle-out ordering of the
remaining roots in actual invariant orbit blocks. Two distinct roots in any
one of these blocks must be orthogonal. The definitions and all invariance and
ordering laws are those of `RootDatumEvenPathGeometry`.

Only the root index type is assumed finite; no finiteness assumption on the
acting group is used. There are no field, characteristic, perfectness or
simple-connectedness assumptions in this combinatorial statement. It supplies
no root-subgroup maps, reflection representatives, or Galois-stable pattern set.
Those remain separate geometric and algebraic obligations of the consumer.
