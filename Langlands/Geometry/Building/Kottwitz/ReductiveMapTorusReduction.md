# Reductive Kottwitz descent from torus existence

This conditional reduction connects the published torus norm and cocenter
reductions to the fixed-group reductive construction of Task 6363. It does not
prove `ReductiveKottwitzExistenceStatement` unconditionally.

`simplyConnectedDerivedKottwitzNaturalAt_of_torus_existence` chooses actual
cocenters using `nonempty_cocenter`. The published canonical fundamental-group
comparison, together with `algebraicFundamentalGroupMap_of_comparison`, supplies
the fundamental-group map statement. The published
`torusFundamentalComparison_proof` supplies the torus comparison. The norm
reduction `simplyConnectedDerivedKottwitz_of_norm_inputs` then constructs the
simply-connected-derived Kottwitz statement using the published
`torusInertiaComparison_proof` and `torusKottwitzExistence`, together with the
retained fundamental-inertia map assumption. Its actual naturality square follows from
`torusKottwitz_natural_of_existence` applied to the induced cocenter morphism.
The preceding cocenter naturality reduction gives naturality upstairs.

`reductiveKottwitzExistenceAt_of_torus_existence` applies the structural
reduction. It supplies z-extension nonemptiness using the unconditional
published `Langlands.GroupScheme.zExtensionExistence`. Upstairs naturality
also supplies the required vanishing on central-torus points and hence on
each projection's point kernel. Descent then gives every conjunct of the
existence statement at the fixed group, including independence and uniqueness
from each individual square.

The remaining explicit assumptions are:

- `FundamentalInertiaMapStatement`;
- point-map surjectivity for every z-extension of the fixed group;
- fundamental-inertia-map surjectivity for every such extension;
- common domination of two z-extensions of that group.

These remain explicit assumptions. The reduction infers no unconditional specification
from the declaration of a selected map. Cocenter choices, z-extension
nonemptiness, fundamental-group comparison and map statements, the torus
fundamental comparison, torus inertia comparison, torus existence and
naturality, and the simply-connected-derived Kottwitz statement are supplied
by the indicated published proofs or their composition with the retained
assumptions.

The provenance is internal composition of the preceding descent and structural
reductions with the published comparison, norm-naturality, cocenter, and
z-extension existence results. The descent follows Kaletha–Prasad (2023),
Lemma 11.5.1, printed p.430 / PDF p.461. Z-extension existence follows
Construction 11.4.1, printed p.428 / PDF p.459, and the norm characterization
is Proposition 11.1.1, printed pp.421–422 / PDF pp.452–453; registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`. The conditional interface and
its explicit assumptions are part of this implementation.
