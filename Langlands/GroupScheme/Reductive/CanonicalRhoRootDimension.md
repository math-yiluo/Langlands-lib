# The root-count upper bound for the canonical induced space

This is derived supporting work by Worker 1369. It identifies the actual
opposite-rho unipotent Lie dimension with the positive-root count of a
supplied pinning and applies the entire-space Frobenius detection bound.
The argument combines existing Library proofs and makes no new assertion
from external literature.

Let `k : Type u` be an arbitrary field and `G` an affine group scheme over
`Spec k`. The first theorem has a supplied connected reductive structure
`hG`, a split torus `T` with inclusion `i : T.toGrp -> G`, a proof `hi` that
`i` is a maximal torus, and a cocharacter `nu` of `T`. There is no
genericity or algebraic-closedness assumption here.

In namespace `Standard`,
`finrank_lieKernel_unipotentScheme_empty` proves

`finrank k (Additive (lieKernel (Standard.unipotentScheme i nu empty) k))
  = Nat.card (positiveRelativeRoots i nu)`.

The group on the left is the actual standard representative of the
unipotent subgroup attached to `nu`. Its intrinsic torus-action weight
spaces form an internal direct sum by
`RelativeRoot.isInternal_actionWeightSpace`. The support comparison
`Standard.actionWeightSpace_unipotentAction_ne_bot_iff` identifies its
nonzero weights with the positive relative roots. That support is finite
by `IsSplitTorus.finite_positiveRelativeRoots`. For each supported weight,
`Standard.finrank_actionWeightSpace_unipotentAction` compares its dimension
with the ambient root space, and `splitRootLieLine` identifies that ambient
space with a one-dimensional vector space. Removing the zero summands
preserves the internal direct sum. The canonical sum map is therefore a
linear equivalence, so its finrank is the sum of one over the finite
support, which is the claimed cardinality. The proof also explicitly
derives finiteness of each supported summand from its dimension one.

The remaining declarations are in namespace `SplitPinning`. Fix a supplied
`p : SplitPinning G` with a `Fintype` root index and full integral coroot
span `hspan : p.rootDatum.corootSpan Int = top`. Write `rho` for
`IntegralWeylVector.rho p.rootDatum p.base hspan`, `nu` for its polarization,
and `U` for `Standard.unipotentScheme p.inclusion (-nu) empty`. The supplied
pinning contains the connected reductive structure, split maximal torus,
actual root datum and base; their universal existence is not assumed by
any theorem in this unit.

`oppositeRhoPositiveRootEquiv` constructs an equivalence

`{s : p.rootIndex // p.base.IsPos s}
  equiv positiveRelativeRoots p.inclusion (-nu)`.

It maps an index `s` to the character `-p.rootDatum.root s`. Negation
preserves actual roots, and the rho sign theorem
`latticePairing_root_polarization_rho_pos_iff` proves positivity for the
opposite cocharacter. Injectivity follows from the root embedding and
injectivity of negation. For surjectivity, negate an arbitrary positive
root of the opposite chamber, express it as a root of the supplied datum,
and use the same pairing sign theorem to show that its index is positive
for the supplied base.

`finrank_lieKernel_oppositeRho` applies the general standard-unipotent
dimension theorem and transports cardinality along this equivalence:

`finrank k (Additive (lieKernel U k))
  = Nat.card {s : p.rootIndex // p.base.IsPos s}`.

These equivalence and Lie-dimension results still hold over an arbitrary
field. The final theorem additionally assumes `IsAlgClosed k`, an
exponential characteristic `q : Nat` with `ExpChar k q`, and an arbitrary
height `r : Nat`. It imposes no positive-height premise.
`finrank_canonicalRhoCovariantSubspace_le_rootCount` gives

`finrank k (p.canonicalRhoCovariantSubspace hspan (q^r - 1))
  <= (q^r) ^ Nat.card {s : p.rootIndex // p.base.IsPos s}`.

The canonical submodule is the entire left-covariant coordinate space for
the canonical negative-rho coordinate at exponent `q^r - 1`. The theorem
rewrites the intrinsic Lie-dimension exponent in
`finrank_canonicalRhoCovariantSubspace_le` using the preceding equality.
The imported `finite_canonicalRhoCovariantSubspace` already proves that
this entire space is finite dimensional through actual same-height
Frobenius restriction. Thus the bound does not arise by assigning finrank
zero to an infinite-dimensional space. The arbitrary field universe `u`
is retained, as are the arbitrary relative tests in the imported
covariance and detection definitions.

The supplied pinning and full coroot span remain explicit hypotheses. The
matching lower bound, irreducibility of the entire canonical space,
universal existence of the supplied data, and the exact
`SteinbergBigCellStatement` remain separate obligations.
