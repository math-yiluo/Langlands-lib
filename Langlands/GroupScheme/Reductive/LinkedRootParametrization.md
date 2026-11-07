# Linked parametrizations of entire intrinsic root subgroups

This derived unit retains both monicity and the literal linked rank-one
relation in the root-map construction for a supplied split root datum. It
first proves that monicity of a triple multiplication implies monicity of
its left and right factors, by inserting identity points in the other factors
on arbitrary relative tests.

For a connected reductive group over any field and a supplied split maximal
torus and root datum, each root admits two monic additive maps with opposite
full-torus characters and the linked rank-one relation. The proof isolates
the root in a cocharacter centralizer, applies the proved semisimple-rank-one
cell theorem, derives monicity of each factor from its open immersion, and
composes with the monic centralizer inclusion. The open-cell assertion is used
only inside that centralizer.

`LinkedRootParametrization` packages actual additive maps representing both
entire intrinsic root subgroups, their opposite torus-equivariance laws, and
their linked rank-one relation on every relative test scheme. For every root
of a supplied split pinning this package exists, and
`SplitPinning.linkedRootParametrization` chooses one. Reducedness of the
pinning's root datum excludes all higher root multiples, and the generic
monic-equivariant-map theorem identifies the full images.

No root maps, rank-one relation, full root images, or open cell in the whole
ambient group are supplied as additional assumptions. The ambient connected
reductive group, split maximal torus, root datum, and (for the final constructor)
split pinning remain explicit inputs. This internal construction is derived
from the imported Library results and uses no new external source.
