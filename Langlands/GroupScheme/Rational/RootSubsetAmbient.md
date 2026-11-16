# Inclusion of either permitted ambient root set

`IsRelativeRootAmbient.subset_relativeRoots` states that either permitted
ambient root set is contained in the actual relative roots. Its inputs are
an arbitrary field, a commutative group scheme mapped into an affine group
scheme, and `IsRelativeRootAmbient i R`. Monicity is not required.

The proof splits the defining alternatives: the full relative root set
contains itself, and membership in the indivisible root set includes
membership in the full set. This shared helper is used by
`UnipotentRootSubsetCocharacterProof` and `StandardRootClosure`; it preserves
the identical lemma from those independently reviewed contributions.
