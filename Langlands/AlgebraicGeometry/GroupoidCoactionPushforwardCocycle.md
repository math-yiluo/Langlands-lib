# Degree-one vanishing for source-cartesian pushforward

This internal algebraic unit extends `GroupoidCoactionPushforward`. Let
`B → D` be a ring map, let `(B,C,t)` and `(D,P,td)` be actual ring étale
equivalence relations, and let `e : P ≃ₐ[D] D ⊗[B] C` describe a
source-cartesian square. Its induced relation-ring map is
`rho = cartesianBaseMap e : C →+* P`. Assume target compatibility
`rho.comp t = td.comp (algebraMap B D)` and the compatible scalar towers
used by the pushforward constructor. For any coaction `theta` on a
`D`-module `M`, degree-one cocycle vanishing for `theta` implies degree-one
vanishing and the published invariant-lifting property `IsAcyclic` for its
pushforward to the underlying `B`-module. Rings lie in an arbitrary universe
`u`; the coefficient module lies in an independent universe `v`.

For a compatible `D`-algebra `S`, `restrictTensorScalars` is the canonical
`S`-linear map `S ⊗[B] M → S ⊗[D] M`, constructed from Mathlib's
`TensorProduct.mapOfCompatibleSMul`. It sends each `s ⊗ m` to the same pure
tensor over `D`. A source-preserving point of the covering relation induces
a base point by composition with `rho`. The source and target
compatibilities ensure that composable covering points induce composable
base points with the same composite target.

The tensor restriction map compares the two specialization maps after the
pushforward tensor equivalence. It also compares the composite coaction maps.
Both identities follow by tensor induction after expressing a covering tensor
as the inverse image of a base tensor. On the resulting generators
`rho(c) ⊗[D] m`, the identities reduce to the pure-tensor formulas.

A cocycle for the pushed coaction can be specialized at these induced base
points even when the test algebra is not flat over `B`, using the existing
universal cocycle specialization theorem. Applying tensor restriction to its
equation gives the covering cocycle equation under the inverse tensor
equivalence. A primitive for this covering cocycle maps to a primitive for
the original base cocycle, since the tensor equivalence carries
`theta(m) - 1 ⊗ m` to the pushed coboundary. Finally, the existing cocycle
vanishing criterion gives `IsAcyclic`, with source flatness supplied by the
base relation's étaleness.

The final two corollaries combine this transfer with
`induced_oneCohomologyVanishes_of_faithfullyFlat`. If the covering relation
has a specified presentation
`D ⊗[invariantRing td] D ≃ₐ[D] P` carrying `1 ⊗ d` to `td(d)`, and `D`
is faithfully flat over `invariantRing td`, then for every module `N` over
that invariant ring the pushforward of the actual induced coaction on
`D ⊗[invariantRing td] N` has degree-one vanishing and is acyclic.
The effective presentation and faithful flatness remain explicit premises.

No geometric source-cartesian presentation, affine quotient, or initial
covering vanishing theorem beyond the cited induced-module result is
constructed here. The module does not prove the host geometric acyclicity
statement.
