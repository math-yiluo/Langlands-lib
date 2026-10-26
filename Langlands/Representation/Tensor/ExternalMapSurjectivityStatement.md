# Surjectivity of the actual external tensor map

Worker 422 authored the statement and initial development draft. Worker 506
prepared this statement pair for independent review. Worker 181 suggested the
coordinate-lifting proof route.

`Langlands.FiniteTensor.ExternalMapSurjectivity R ι H V W` is a proposition
asserting that every family of surjective factor intertwiners induces a
surjective `Langlands.FiniteTensor.externalMap`. Its parameters have five
independent universes:

| Parameter | Assumptions |
| --- | --- |
| `R : Type uR` | `CommRing R` |
| `ι : Type uI` | Arbitrary index type, including the empty type |
| `H : ι → Type uG` | `∀ i, Group (H i)` |
| `V : ι → Type uV` | `∀ i, AddCommGroup (V i)` and `∀ i, Module R (V i)` |
| `W : ι → Type uW` | `∀ i, AddCommGroup (W i)` and `∀ i, Module R (W i)` |

For every `ρ : ∀ i, Representation R (H i) (V i)`,
`σ : ∀ i, Representation R (H i) (W i)`, and
`f : ∀ i, (ρ i).IntertwiningMap (σ i)`, its exact assertion is

```lean
(∀ i, Function.Surjective (f i)) →
  Function.Surjective (externalMap f)
```

The map is the existing actual Library intertwiner between the external
representations on `PiTensorProduct R V` and `PiTensorProduct R W`.
Its underlying linear map is definitionally
`PiTensorProduct.map (fun i => (f i).toLinearMap)`. The source and target
carrier universes remain independent, and no nonempty-index assumption is
present.

Provenance is internal algebraic reasoning from the Library construction in
[Finite](Finite.md) and Mathlib's indexed tensor product. In pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean` defines `map` and proves
`map_tprod` and `PiTensorProduct.induction_on`. The induction principle reduces
surjectivity to scalar multiples of pure tensors and addition: coordinatewise
surjectivity supplies preimages of each pure-tensor coordinate. This explains
the proposed algebraic assertion; the paired Lean file defines its statement.

There are no topology, smoothness, finiteness, finite-dimensionality, flatness,
irreducibility, or classification hypotheses. The assertion concerns the
algebraic tensor map; smooth-induction surjectivity and exactness of a
normalized product functor are separate statements.

The sole direct import is `Langlands.Representation.Tensor.Finite`. Its
project import closure consists of the representation category, foundational
smoothness definitions, smooth-part definitions/basic statement/basic proof,
and continuous-pullback statement/proof. These elementary constructions and
proofs do not import segment-product uniqueness, special-head classification,
multisegment exhaustion, ordered-head existence, quotient coverage, ordered
conversion, or tempered/square-integrable classification or exhaustion.
