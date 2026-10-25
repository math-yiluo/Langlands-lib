# Cyclic evaluation for commuting actions

This module constructs compatible finite tensor evaluations and their induced
map on an algebraic restricted tensor product. All declarations are in
`Langlands.RestrictedTensor.CyclicEvaluation`.

## Data, scope, and provenance

Let `K : Type uK` be a field, `ι : Type uI` an arbitrary index type,
`G : ι → Type uG` a family of monoids, and `V : Type uV` a `K`-vector
space. Given representations `σ i : Representation K (G i) V`,
`Commuting σ` means

```text
σ i g (σ j h x) = σ j h (σ i g x)
```

for distinct `i, j` and all `g, h, x`. Fix `hσ : Commuting σ` and
`v : V`. `Factor σ v i` abbreviates the carrier of
`(Langlands.Cyclic.orbitSpan (σ i) v).toSubmodule`. Its universe is
explicitly `Type uV`, independently of the other three universes. Write
`e i := Langlands.Cyclic.generator (σ i) v`.

There are no assumptions of nonvanishing, topology, irreducibility,
finite-dimensionality, or tensor factorization. In particular, `v = 0`,
empty finite stages, and an empty index type are allowed. The restricted
tensor construction uses the generalized `RestrictedTensor.Space`, which
accepts arbitrary reference vectors. This module does not establish
injectivity or surjectivity of its evaluation maps.

The provenance is internal: these definitions and proofs are derived from the
published [cyclic-span presentation](../CyclicSpan.md), the published
[restricted tensor construction](Basic.md), and Mathlib's monoid-algebra,
finite-product, multilinear-map, and projective-vector-space APIs. No
separately numbered result in the literature is asserted for these names.
The construction is an algebraic prerequisite for the separate Flath
existence argument.

## Finite products and descent

`algebra_commute` extends the commuting-action hypothesis to arbitrary
elements of two distinct monoid algebras. The proof performs linear
monoid-algebra induction in both arguments; singleton monomials reduce to
`hσ` and commuting scalar multiplication.

`algebraProduct σ hσ S a` is `Finset.noncommProd` of the endomorphisms
`(σ i).asAlgebraHom (a i)` for `i ∈ S`. Its pairwise-commutativity proof
comes from `algebra_commute`. Thus the definition does not depend on a chosen
ordering of `S`. `algebraProduct_empty` gives the identity endomorphism;
`algebraProduct_insert` and `algebraProduct_insert_right` place a fresh
coordinate on either side. `algebraProduct_congr` ignores changes outside
`S`, and `algebraProduct_erase_right` isolates one existing coordinate.

`commute_algebraProduct` proves that a fresh coordinate algebra action
commutes with the whole product. Applying this equality to `v` proves
`relation_annihilates`: if `(σ i).asAlgebraHom a v = 0`, then that same
operator kills `algebraProduct σ hσ S b v` whenever `i ∉ S`.

The stronger comparison law `algebraProduct_congr_eval` says the value at
`v` depends only on the vectors `(σ i).asAlgebraHom (a i) v`, for `i ∈ S`.
Its proof inducts on the finite set, replaces the remaining factors by the
induction hypothesis, and commutes the isolated coordinate to the right so
its value on `v` can be replaced. This establishes descent through all
relations in the individual cyclic presentations.

## Multilinearity and finite-stage evaluation

`presentationSection σ v i` is a classical linear right inverse of the
surjective map `Langlands.Cyclic.presentation (σ i) v`. Its existence
uses projectivity of vector spaces; no basis is an input to the construction.
`presentation_section` is the right-inverse identity, and
`presentationSection_eval` is its equality in `V`.

For a finite tuple `x : ∀ i : S, Factor σ v i`,
`tupleAlgebra σ v S x` uses these presentations on `S` and zero elsewhere.
`tupleAlgebra_mem` gives its value at a member of `S`. `tupleEval` applies
their finite algebra product to `v`.

`tupleEval_update` places an updated coordinate on the right using
`algebraProduct_erase_right`. The remaining product ignores the update,
and the right-inverse identity replaces the final presented vector by the
updated vector itself. The result is one fixed linear endomorphism applied
to that coordinate. Its additivity and scalar-linearity give
`evalMultilinear`.

`evalStage σ hσ v S` is the `PiTensorProduct.lift` of this multilinear
map:

```text
RestrictedTensor.Stage K (Factor σ v) S →ₗ[K] V.
```

`evalStage_tprod` gives its elementary-tensor value. More generally,
`evalStage_presentation` states

```text
evalStage σ hσ v S
  (tprod K (fun i : S => Cyclic.presentation (σ i) v (a i)))
  = algebraProduct σ hσ S a v.
```

It follows from `algebraProduct_congr_eval` and the section identities.
`evalStage_unique` proves that this formula uniquely determines the linear
map: tensor extensionality reduces to a finite tuple, each coordinate of
which is presented by its chosen section. Consequently the implementation
choices do not affect the characterized map.

## Transition coherence and normalization

`algebraProduct_subset` shows that enlarging `S` to `T` changes no product
when new algebra elements are one. Its proof splits `T` into the disjoint
union of `S` and `T \ S` and evaluates the complementary product.
`algebraProduct_subset_eval` only requires the new operators to fix `v`,
and the old operators to agree on `v`. It first replaces the family using
`algebraProduct_congr_eval`, then applies `algebraProduct_subset`.

`tupleEval_extend` applies this law to adjoining the distinguished cyclic
generators. On new coordinates the section evaluates to `v`; on old
coordinates it evaluates to the original vector. Tensor extensionality
therefore proves `evalStage_transition`, the equality of linear maps

```text
(evalStage σ hσ v T).comp (RestrictedTensor.transition e hST)
  = evalStage σ hσ v S
```

for every inclusion `hST : S ⊆ T`.

`tupleEval_generator` compares an all-generator tuple with the empty
product. It gives `evalStage_generator`, whose value is `v`.
`evalStage_empty` sends every empty elementary tensor to `v`.
`evalStage_empty_scalar` states the full scalar formula

```text
evalStage σ hσ v ∅ x = PiTensorProduct.isEmptyEquiv ... x • v.
```

The latter proof uses tensor induction, linearity, and the empty-product
formula. In particular, the scalar-one empty tensor maps to `v`.

`orbitVector σ v i g` is the restricted action of `g` on the distinguished
generator, and `orbitVector_val` identifies its underlying vector with
`σ i g v`. `actionProduct σ hσ S g` is the enumeration-independent
`Finset.noncommProd` of the monoid operators `σ i (g i)`. The formula
`evalStage_orbit` identifies evaluation of their pure orbit tensor with
`actionProduct σ hσ S g v`. The proof uses singleton monoid-algebra
presentations and `evalStage_presentation`.

## Coordinate equivariance and the limit map

For `i : S`, `coordinateAction σ v S i g` is `PiTensorProduct.map` of
the identity maps with coordinate `i` replaced by
`(Langlands.Cyclic.orbitSpan (σ i) v).toRepresentation g`.
`coordinateAction_tprod` gives its coordinate-update formula.
`tupleEval_coordinate` commutes this coordinate operator past the
complementary product from `tupleEval_update`. Tensor extensionality gives
`evalStage_coordinateAction`:

```text
(evalStage σ hσ v S).comp (coordinateAction σ v S i g)
  = (σ i g).comp (evalStage σ hσ v S).
```

`insertAction σ v S i g` first uses the transition to `insert i S`, then
acts on coordinate `i`. Associativity of composition, coordinate
equivariance, and transition coherence prove `evalStage_insertAction`.
It applies to every `i`, including a fresh coordinate.

For any exceptional finite set `E`, `eval σ hσ v E` uses
`RestrictedTensor.lift` on the compatible family `evalStage`:

```text
RestrictedTensor.Space K (Factor σ v) E e →ₗ[K] V.
```

`eval_of` gives its value on a finite-stage representative, and `eval_pure`
gives its value on a pure tensor. `eval_generator` then proves that every
all-generator pure tensor at every stage containing `E` evaluates to `v`.
These are consequences of the constructed lift and the proved finite-stage
laws, without assumptions on bijectivity or on a factorization equivalence.
