# Actual equivariant archimedean symmetrization

This internal specialization applies the constructed generic symmetrization to
the entire actual complexified archimedean matrix Lie algebra. It retains every
field universe and every natural rank, including zero. No number-field
assumption is required for these algebraic constructions.

`LieSymmetricPower d` is Mathlib's actual symmetric tensor quotient of degree
`d`. `lieSymmetricPowerConjugation d g` applies the published complex adjoint
map to each factor. Its inverse applies the adjoint of `g⁻¹`. Pure-tensor
extensionality verifies the inverse, identity and multiplication laws using the
corresponding actual Lie conjugation identities. These laws give
`lieSymmetricPowerRepresentation`, an algebraic representation of the full
archimedean group. Its definition includes all components of that group; it
asserts no topological regularity.

`envelopingSymmetrize d` is the generic normalized permutation average descended
to this actual symmetric quotient. `envelopingSymmetrize_tprod` gives the
averaged product of genuine Lie generators. Its image belongs to the genuine
enveloping degree piece `d`, so `envelopingSymmetrizeDegree d` restricts the
codomain to that submodule.

`envelopingSymmetrize_conjugation` proves full-group equivariance by the
generic naturality theorem and the published identity for conjugation of a
genuine enveloping generator. `envelopingSymmetrizeDegree_conjugation` gives the
same identity within the degree piece. Thus these maps intertwine the actual
symmetric-power and degree-piece representations.

`envelopingSymmetrize_tprod_sub_orderedWord_mem` specializes the characteristic
zero comparison: symmetrization of a pure tensor differs from the ordered
generator product by an element of degree at most `d - 1`. This includes `d = 0`,
where the difference is zero.

The provenance is the generic quotient and symmetrization constructions and
the actual matrix adjoint lift imported here. This unit does not identify the
direct sum of the symmetric powers with the symmetric algebra, prove a PBW
isomorphism or central generation, or prove automorphic differential growth.
