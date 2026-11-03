# The kernel of a subgroup-preimage projection

For homomorphisms `q : G → Q` and `j : H → Q` over the same arbitrary scheme
base, `SubgroupPreimage.kernelIso q j` constructs an actual group-scheme
isomorphism

`kernel (SubgroupPreimage.projection q j) ≅ kernel q`.

The construction pastes two pullback squares in the category of group schemes:
the defining kernel square of the preimage projection and the defining
preimage square of `q` and `j`. The composite of the unit homomorphism of
`H` with `j` is the unit homomorphism of `Q`, by uniqueness of homomorphisms
from the trivial group. The pasted square therefore represents the original
kernel of `q`. Uniqueness of pullbacks gives the isomorphism. No closedness,
monomorphism, flatness or surjectivity assumption on either map is needed.

`kernelIso_hom_comp` retains the inclusions into `G`, while `kernelOverIso`
forgets only the group law. Affineness of the full original kernel transfers
through this isomorphism over the base. Over a field, the existing
coefficient-representation unipotence predicate transfers along the group
isomorphism. `quasiCompact_projection` separately records preservation of
quasi-compactness under the actual preimage square.

This internal derived construction uses the published actual kernels,
subgroup-preimages and unipotence transport, together with categorical
pullback pasting. It makes no quotient existence or affineness claim for
the target `Q`.
