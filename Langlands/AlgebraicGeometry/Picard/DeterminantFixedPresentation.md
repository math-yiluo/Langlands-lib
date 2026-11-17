# Fixed-index presentations of the actual finite locally free determinant

This internal unit compares a determinant presentation formed from a
fixed finite-index frame cover with the existing actual
`finiteLocallyFreeDeterminant`. Let `M` be a module sheaf on a scheme
`X`, and specify actual free frames on a covering family `T i`, all
indexed by one finite type `I`.

`relabelFrame` reindexes an actual sheaf frame along an equivalence of
finite index types. The theorem `relabelFrame_basis` identifies its
actual section basis with the correspondingly relabeled original basis;
the proof uses the free sheaf's generator universal property.

`normalizedFrames` replaces `I` by `ULift (Fin (card I))` on every
chart. This is a `FiniteLocalFrames M` object for the existing actual
determinant construction. Its section bases, after the construction's
removal of `ULift`, are the original bases reindexed by
`Fintype.equivFin I`. Simultaneously reindexing both indices of a
transition matrix preserves its determinant. Consequently
`normalizedFrames_cocycle` identifies the variable-rank construction's
cocycle for these normalized frames with the fixed-index cocycle.

For any supplied `HasFiniteLocalBasis M` witness, the definition
`finiteDeterminantPresentationIso` gives an actual line-bundle
isomorphism from `DeterminantFrames.lineBundle e hT` to the existing
`finiteLocallyFreeDeterminant hM`. It first identifies the normalized
and original cocycle lines, then applies the existing comparison from
any finite frame presentation to the chosen determinant.

The provenance is internal. This is a compatibility result between two
existing determinant presentations. A fixed-index cover is an input;
the unit does not claim that every finite locally free sheaf admits a
global cover of one fixed rank.
