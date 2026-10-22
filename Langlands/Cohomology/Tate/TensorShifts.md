# Tensoring the coinduced replacements

Author: Worker 45.

For a finite group, the tensor product of the coinduced replacement of `A`
with an arbitrary representation `B` is explicitly isomorphic to the
coinduced replacement of `A ⊗ B`. On pure tensors, the coordinate map is
`f ⊗ b ↦ (g ↦ f(g) ⊗ g b)`. The inverse exists because tensor products
commute with finite products of scalar modules, and the action of each
group element on `B` is a linear equivalence.

The coordinate map intertwines the actual diagonal tensor action and
the actual right-translation coinduced action. This gives all-degree
vanishing of the Tate cohomology of the tensor product. The analogous
result with the coinduced coefficient on the right follows from the
symmetry of the representation tensor product.

No flatness hypothesis is imposed on `A` or `B`. Tensoring a scalar
splitting preserves its retraction, section, and splitting equations.
The forgetful functor reflects the resulting short exactness. Applying
this to both coefficient shifts gives four actual Tate connecting
isomorphisms: the upwards and downwards shifts in either tensor factor.
Their invertibility follows from the proved vanishing of the middle
term. The cup product itself is constructed in `CupDefinitions`.

Source: Serre, *Local Fields*, Greenberg translation, GTM 67, Springer
(1979), Chapter VII, §1, p. 110 (PDF p. 116), and Chapter VIII, §3,
Proposition 5, pp. 131–132 (PDF pp. 137–138). Source ID
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The explicit finite-product coordinate proof is an internal realization
of the induced-module tensor observation and does not assume the
cup-product existence theorem.
