# Relative dimension sublevels and the quasi-finite locus

Worker 105 constructs the actual source sets where local dimension in the
residue-field scheme fibre is at most a natural number. The dimension is
`relativeTopologicalKrullDimAt`, independently constructed from the minimum
dimension of actual open neighbourhoods. The sets increase with the bound.
These are the sets in Stacks Lemma 29.29.4, tag 02FW, of the registered source
`stacks-fibre-constructibility-local-dimension-2026-11-04`, SHA-256
`1f3421cf5c5733cafdf296e8a9d38af7e4730550989a3d727d4b9a61cf1f3db3`.
This is a prerequisite for Conrad Theorem 3.4(2), rather than its descent proof.

The additional bridge is derived from Mathlib's Artinian-scheme and
quasi-finiteness results. On a locally Noetherian scheme, local dimension at
most zero is equivalent to openness of the actual singleton. For the forward
implication, take an open neighbourhood attaining the minimum. Dimension at
most zero makes this locally Noetherian open scheme locally Artinian, hence
discrete. Its point singleton is open and the open immersion maps it to the
ambient singleton. Conversely, an open singleton is a subspace with at most
one point and dimension at most zero, giving the local bound.

The fibres of a locally finite-type morphism are locally Noetherian schemes
over their actual residue fields. Applying the bridge and Mathlib's criterion
`quasiFiniteAt_iff_isOpen_singleton_asFiber` identifies the sublevel at zero
with the actual quasi-finite locus. Mathlib's Zariski main theorem proves that
this locus is open. Thus the `n = 0` case of Stacks Lemma 29.29.4 is proved for
arbitrary locally finite-type morphisms, without separatedness or
quasi-compactness. This conclusion concerns a varying family of fibres.

Finally, all fibres having componentwise pure dimension zero is equivalent
to local quasi-finiteness. The existing pure-dimension comparison converts
the former into constancy of local relative dimension at zero. The bridge
handles the upper bound; the dimension of a nonempty open neighbourhood is
nonnegative, giving equality. Empty fibres satisfy pure dimension vacuously,
and no surjectivity is added.

Openness at positive bounds, retrocompactness for locally finitely presented
morphisms, and general fibre-locus constructibility remain separate results.
