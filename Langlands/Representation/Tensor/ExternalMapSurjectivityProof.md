# Surjectivity of external tensor maps: proof

Worker 422 wrote the Lean proof, which this file reproduces unchanged. Worker
181 suggested the scaled-pure-tensor route while coordinating induction
surjectivity. Worker 256 rechecked the proof against the published statement
and wrote this account of it.

## Result

`Langlands.FiniteTensor.externalMapSurjectivity` proves the Library
proposition `Langlands.FiniteTensor.ExternalMapSurjectivity R ι H V W` from
[ExternalMapSurjectivityStatement](ExternalMapSurjectivityStatement.md). The
module's only import is that statement module. The theorem has the same
parameters as the statement, in the same order, and five independent universe
parameters `uR uI uG uV uW`:

```lean
(R : Type uR) [CommRing R] (ι : Type uI)
(H : ι → Type uG) [∀ i, Group (H i)]
(V : ι → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
(W : ι → Type uW) [∀ i, AddCommGroup (W i)] [∀ i, Module R (W i)]
```

So for every commutative ring `R` and every index type `ι` (the empty type
included), surjective factor intertwiners `f i` give a surjective actual
external tensor map `Langlands.FiniteTensor.externalMap f`. The theorem adds
no hypotheses: no topology, smoothness, finiteness, finite-dimensionality,
flatness, irreducibility or classification. It concerns only the algebraic
tensor map. Smooth-induction surjectivity and exactness of a normalized
product functor are separate results.

## Implemented proof

1. Introduce the representations `ρ` and `σ`, the intertwiners `f`, the
   factorwise surjectivity hypothesis `hf`, and a target tensor `y`.
2. `externalMap f` is defined in
   [Finite](Finite.md) as `Langlands.FiniteTensor.map` applied to the factor
   intertwiners rebuilt over the product group. Their underlying linear maps
   are the `(f i).toLinearMap`, and `map` has underlying linear map
   `PiTensorProduct.map`. A `change` therefore restates the goal as
   `∃ x, PiTensorProduct.map (fun i => (f i).toLinearMap) x = y`. This holds
   by definitional unfolding alone.
3. Apply Mathlib's `PiTensorProduct.induction_on` to `y`. It has two cases:
   scalar multiples of pure tensors, and sums. Zero needs no separate case.
4. Case `smul_tprod a v`, where `y = a • tprod R v`. `choose` applied to
   `fun i => hf i (v i)` gives a family `w` with `hw i : f i (w i) = v i`. The
   proposed preimage is `a • tprod R w`. `simp only [map_smul,
   PiTensorProduct.map_tprod]` rewrites its image to
   `a • tprod R (fun i => (f i).toLinearMap (w i))`, whose coordinates are the
   values `f i (w i)`. Then `congrArg` applied to `funext hw` identifies this
   with `a • tprod R v`.
5. Case `add x y hx hy`. Take preimages `x'` of `x` and `y'` of `y` from the
   induction hypotheses. Then `x' + y'` is a preimage of `x + y` by `map_add`
   and these two equalities.

The coordinate choice in step 4 needs no restriction on `ι`. When `ι` is
empty, `w` is the empty family.

## Provenance

This is internal algebraic reasoning from the existing Library construction.
No original literature is cited. It uses the following facts from Mathlib at
the pinned commit `5ed2965256430c3649e86755f9576b54eca72435`, all in
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean`:

- the indexed tensor map `PiTensorProduct.map`;
- its value on pure tensors, `PiTensorProduct.map_tprod`;
- the induction principle over scaled pure tensors and sums,
  `PiTensorProduct.induction_on`.

`map_smul` and `map_add` are the generic linearity lemmas. The proof uses no
representation-theoretic classification and no smooth-induction surjectivity.

The statement module's project import closure has eight modules: the
foundational smoothness definitions, the representation category, the
smooth-part definitions, basic statement and basic proof, the
continuous-pullback statement and proof, and
`Langlands.Representation.Tensor.Finite`. None of them imports segment-product
uniqueness, special-head classification, multisegment exhaustion, ordered-head
existence, quotient coverage, ordered conversion, or tempered or
square-integrable classification or exhaustion.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, development compilation
of this module gave no errors or warnings. Inspection of the theorem reported
exactly the axioms `propext`, `Classical.choice` and `Quot.sound`. A separate
private check confirmed that the theorem has the full parameter telescope
above, ending in `ExternalMapSurjectivity R ι H V W`. These checks are not
independent acceptance.
