# Jordan components of locally finite derivations

This module proves that the compatible semisimple component of a locally finite
derivation over a perfect field is an actual derivation. The complementary
component is therefore also a derivation. The field and the algebra have
independent arbitrary universes. The algebra is commutative; its dimension
may be infinite, and no smoothness, finite-type or reducedness condition is
imposed. Local finiteness of the original derivation's linear endomorphism
is an explicit premise.

## Finite tensor-sum compatibility

`isSemisimple_map_end` transports semisimplicity of a finite-dimensional
endomorphism through an arbitrary algebra homomorphism into an endomorphism
algebra. Its squarefree minimal polynomial remains an annihilator after that
map. The target space need not be finite dimensional.

`tensor_legs_commute` proves directly on pure tensors that endomorphisms on
the two tensor factors commute. `tensorSum f g` is the sum of those two tensor
legs. When both factors are finite dimensional and the field is perfect,
the tensor sum of semisimple endomorphisms is semisimple: transport through
the tensor algebra homomorphisms proves semisimplicity of each leg, and
Mathlib's commuting-sum theorem applies.

`jordanSemisimplePart_tensorSum` proves that the canonical finite semisimple
component of a tensor sum is the tensor sum of the canonical semisimple
components. The tensor sum of the nilpotent components is nilpotent because
the two legs commute. The semisimple sum is semisimple, and the two sums
commute, by commutation within each finite Jordan decomposition and between
the tensor legs. Their sum is the original tensor sum. Jordan uniqueness
therefore gives the identity.

## Derivation components

For finite subspaces invariant under the original derivation `D`,
`mulMap_intertwines` expresses the Leibniz rule as a linear intertwiner from
the tensor-sum action on those subspaces to `D` on the ambient algebra. This
identity requires only a field, without perfection or local finiteness.

`semisimplePart_leibniz` chooses finite invariant subspaces through each of two
algebra elements. The finite-source naturality theorem from
`LocallyFiniteJordan` identifies the global semisimple component after the
multiplication map with the finite canonical component of the tensor sum.
The tensor-sum identity and agreement of the global component with its finite
restrictions give the Leibniz formula for those two elements.

`semisimplePart` bundles the global component as a derivation using this
Leibniz identity. `nilpotentPart` is its difference from the original
derivation. Their underlying linear maps are respectively exactly
`locallyFiniteSemisimplePart` and `locallyFiniteNilpotentPart`, as the final
two identities state. In particular the earlier vectorwise local-nilpotence
result applies to the latter linear map; no uniform nilpotence exponent is
asserted.

## Provenance and scope

This is derived content using the compatible global Jordan construction,
Mathlib's finite Jordan uniqueness, squarefree-annihilator semisimplicity,
commuting sums, tensor algebra homomorphisms and the submodule multiplication
map. It assumes no external structural theorem. Perfection and local
finiteness remain explicit hypotheses. The module does not prove local
finiteness for a particular group-scheme translation derivation, representation
compatibility of its evaluated Lie element, or Cartan generation.
