# Finite-product pointwise smooth-induction tensor map

Author: Worker 173.

This is an internal universal-property construction from the published actual
smooth-induction module and Mathlib's indexed tensor product. It constructs a
canonical equivariant linear map

\[
\bigotimes_{i\in\iota}\operatorname{Ind}_{P_i}^{G_i}(\sigma_i)
\longrightarrow
\operatorname{Ind}_{\prod_i P_i}^{\prod_i G_i}
  \left(\boxtimes_i\sigma_i\right).
\]

The coefficient ring `R` is any commutative ring, the index type `ι` has an
instance `[Finite ι]`, the `G i` are topological groups, and `P i` are arbitrary
subgroups. The coefficient modules `V i` are arbitrary modules with additive
commutative group structure. No topology is placed on them. The input
representations need not be smooth. There is no assumption of finite
dimensionality, admissibility, irreducibility, compact quotient, or a supplied
equivalence. No injectivity or surjectivity is asserted.

The subgroup is literally `Subgroup.pi Set.univ P` of the actual product group,
not a substitute isomorphic group. `productSubgroupCoordinate P i` sends an
element of this subgroup to its `i`th coordinate in `P i`. `productInducing P σ`
is `FiniteTensor.external σ` pulled back through the tuple of these coordinate
homomorphisms. `productInducing_tprod` exposes its factorwise action.

`pointwiseTensorFunctions P σ` is the multilinear map into all functions on the
product group. It is formed with `MultilinearMap.pi` by composing
`PiTensorProduct.tprod R` with the linear factor evaluation maps. Its value is

\[
(f_i)_i\longmapsto\left[g\longmapsto\bigotimes_i f_i(g_i)\right].
\]

`pointwiseTensorFunctions_covariant` proves covariance under the actual product
subgroup by factor covariance and the pure-tensor action formula.
`pointwiseTensorFunctions_uniform` chooses an open right stabilizer `K i` of
each entire factor function. It takes the actual subgroup
`Subgroup.pi Set.univ (fun i => (K i).toSubgroup)` as the stabilizer in the
product. `isOpen_set_pi Set.finite_univ` proves openness. Each coordinate lies
in its chosen stabilizer, so this one product subgroup fixes the whole
pointwise pure product uniformly for all `g`.

Two applications of `MultilinearMap.codRestrict` restrict the pointwise map
first to covariant functions and then to smooth vectors. The result is
`pointwiseTensorMultilinear P σ`, whose linear extension by
`PiTensorProduct.lift` is `finiteProductTensorMap P σ`. Its type is the actual
`Representation.IntertwiningMap` from
`FiniteTensor.external (fun i => smoothInduced (P i) (σ i))` to
`smoothInduced (Subgroup.pi Set.univ P) (productInducing P σ)`.
The intertwining field is proved by extensionality on pure tensors. Right
translation of each input evaluates to `f i (x i * g i)`, which is also right
translation of the output function. No equivariance or multilinearity
certificate is assumed as external input.

The usable simp lemma `finiteProductTensorMap_tprod_eval` states exactly

```text
eval (Subgroup.pi Set.univ P) (productInducing P σ)
  (finiteProductTensorMap P σ (PiTensorProduct.tprod R f)) g
  = PiTensorProduct.tprod R (fun i => eval (P i) (σ i) (f i) (g i)).
```

All four universes `uR`, `uI`, `uG`, and `uV` remain independent. The product
group lives in `Type (max uI uG)`, the inducing tensor module in
`Type (max uR uI uV)`, and both the source tensor of smooth functions and the
target smooth-function carrier in `Type (max uR uI uG uV)`. No universe
resizing is imposed. The construction includes the empty family, hence
`Fin 0`: product membership and coordinate equalities are vacuous, the empty
product stabilizer is the whole group, and the tensor universal property
still applies. No coordinate is selected by any part of the argument.

The mathematical provenance is internal: the covariance and right-translation
conventions are those of `Langlands.Representation.Induction.Definitions`, and
the external action is `Langlands.Representation.Tensor.Finite`. The construction
uses `tprod` and `lift` from `Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`,
`pi`, `compLinearMap`, and `codRestrict` from
`Mathlib/LinearAlgebra/Multilinear/Basic.lean`, the actual subgroup product, and
finite-product openness. The prepared environment pins Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` and Lean 4.34.0. This pair does not
attribute the unrestricted map or a tensor-induction isomorphism to an
external literature theorem.

The module compiles without warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection of the map confirms its four
independent universe parameters and an axiom closure consisting only of
`propext`, `Classical.choice`, and `Quot.sound`. Development compilation and
inspection are separate from independent semantic review and publication.
