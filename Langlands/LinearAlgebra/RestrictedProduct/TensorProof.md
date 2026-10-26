# Restricted-product tensor scalar comparison and bijectivity: proof

Worker 288 formalized this proof. Worker 98 suggested the full-product and
coordinate-submodule argument in the task specification. The scalar comparison
and final reduction are adapted from Matthew Jasper's Imperial FLT source
cited below; the middle argument is an internal alternative to its direct-limit
proof.

## Exact theorem and hypotheses

The module imports the unchanged published statements and maps through
`Langlands.LinearAlgebra.RestrictedProduct.TensorStatement`, and the published
arbitrary-product proof through
`Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof`. Its exported theorem is

```lean
theorem RestrictedProduct.tensorRestrictedProductComparison_proof.{uR, uM, uι, uN} :
  RestrictedProduct.TensorRestrictedProductComparison.{uR, uM, uι, uN}
```

There are no term parameters outside the target. The four universes are
independent: `R : Type uR`, `M : Type uM`, `ι : Type uι`, and
`N : ι → Type uN`. The target is `A ∧ (B ∧ C)`, with data quantified
separately in each clause:

1. For commutative rings `R`, `M` with `Algebra R M`, and rings `N i` with
   `Algebra R (N i)`, the underlying functions satisfy
   `⇑(lTensorLeft R M N ℱ L) = lTensor R M N ℱ L`. This clause has no
   flatness or finite-presentation hypothesis.
2. For a commutative ring `R`, additive commutative groups `M` and `N i`
   with their `R`-module structures, and
   `[Module.FinitePresentation R M] [Module.Flat R M]`,
   `Function.Bijective (lTensor R M N ℱ L)` holds. Neither `M` nor the
   `N i` require ring or algebra structures here.
3. Under the ring and algebra hypotheses of clause A and
   `[Module.Flat R M] [Module.FinitePresentation R M]`,
   `Function.Bijective (lTensorLeft R M N ℱ L)` holds.

In every clause `ι`, `L : ∀ i, Submodule R (N i)`, and `ℱ : Filter ι`
are arbitrary. In particular, there is no finite-index, nonempty-index,
`NeBot`, cofinite-filter, freeness, projectivity, or assumed-bijectivity
hypothesis. Principal filters and the bottom filter are included.

The maps have the actual restricted-product codomains from `Tensor.lean`.
`rangeLTensor R M N L i` is the image of
`(L i).subtype.lTensor M : M ⊗[R] L i →ₗ[R] M ⊗[R] N i`.
Under the algebra hypotheses, `rangeLTensorLeft` has the same underlying
set definitionally, although it is recorded as an `M`-submodule. Thus the
function equality in A takes place in the definitionally identified actual
restricted-product carriers.

## Scalar comparison

The private theorem `scalar_comparison` is precisely clause A with its
quantified data introduced. Function and restricted-product extensionality
reduce equality to one coordinate of one tensor. `TensorProduct.inductionOn`
reduces this to pure tensors and addition. The published
`lTensorLeft_tmul` formula and the defining formula of `lTensor` identify both
pure-tensor values with `m ⊗ x i`; additivity finishes the sum case. This is
the argument of the original source at lines 93–100.

## General module bijectivity

The private theorem `restricted_bijective` supplies clause B. It introduces
only local linear maps and two local commutative-square equalities.

For injectivity, write `X = Πʳ i, [N i, L i]_[ℱ]`, let `Y` be the target
restricted product, and let `j : X →ₗ[R] ∀ i, N i` and
`k : Y →ₗ[R] ∀ i, M ⊗[R] N i` be the coordinate inclusions. The map `j`
is injective by subtype extensionality. On pure tensors the equality

```text
k ∘ lTensor = piRightHom R R M N ∘ (j.lTensor M)
```

is definitional, so `TensorProduct.ext'` proves it for linear maps.
Flatness makes `j.lTensor M` injective by Mathlib's
`Module.Flat.lTensor_preserves_injective_linearMap`. The published
`RestrictedProduct.tensorPiComparison_proof R M N` makes the full-product
comparison injective. Their composite is injective, hence so is `lTensor`:
apply `k` to an equality of outputs and use the composite's injectivity.
No injectivity of a tensor-inclusion image map is assumed.

For surjectivity, fix `y : Y`. Define a coordinate submodule, depending on
this output, by

```text
P i = L i   if y i ∈ rangeLTensor R M N L i,
      ⊤     otherwise.
```

For each `i` choose `z i : M ⊗[R] P i` whose image under
`(P i).subtype.lTensor M` is `y i`. In the first branch this is exactly
membership in `rangeLTensor`. In the other branch the inclusion of the top
submodule is surjective; `LinearMap.lTensor_surjective` supplies the tensor
preimage. Explicit equalities `P i = L i` or `P i = ⊤` transport these
existential statements. Classical choice assembles the coordinate preimages
into `z : ∀ i, M ⊗[R] P i`.

There is a local linear map `e : (∀ i, P i) →ₗ[R] X` sending a family of
submodule elements to their ambient coordinates. It lands in `X` because
`y.property` says that `y i` belongs to the range submodule for
`ℱ`-eventually every `i`. At each such index `P i = L i`, so every input
coordinate belongs to `L i`. The implementation uses this submodule equality
as an inclusion to transport membership without changing the dependent
coordinate type. Additivity and scalar compatibility of `e` are definitional.
This argument uses eventual membership directly and also applies to `ℱ = ⊥`.

Let `q` apply `(P i).subtype.lTensor M` in each coordinate. A second
`TensorProduct.ext'` computation proves the naturality equality

```text
k ∘ lTensor ∘ (e.lTensor M) =
  q ∘ piRightHom R R M (fun i ↦ P i).
```

Apply the surjectivity part of the published arbitrary-product comparison
to the family of modules `P i` to obtain `t` mapping to `z`. Then
`e.lTensor M t` is a preimage of `y`. Restricted-product extensionality,
the naturality equality, the equation for `t`, and the chosen equations
for `z i` prove this coordinatewise. Finite presentation is used through
the two product-comparison applications; flatness is used in injectivity.
All submodule and product module structures are existing instances.

These two private theorems contain exactly the proof obligations used by
the exported conjunction. They introduce no separately exported construction
or substantial independent API.

## Final clause and scope

The exported theorem introduces each clause's own data and uses the two
private results. For clause C, rewriting by `scalar_comparison` turns the
underlying-function bijectivity goal into `restricted_bijective`. This is
the reduction used by the original `lTensorLeft_bijective`.

The module proves the exact three-clause target. Equivalence packaging,
inverse laws, topology, norms, and number-field specializations are outside
this result. The arbitrary-product theorem is imported, not duplicated.
The statement pair, canonical-map pair, and their imports are unchanged.

## Provenance and modifications

The originating source is Matthew Jasper,
[`FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean),
ImperialCollegeLondon/FLT commit `923d45174c500aa1d994ba973bac38ea39eacbf7`,
Copyright (c) 2025 Matthew Jasper, Apache-2.0. Its complete 259 lines were
read in registered source `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `ImperialCollegeLondon--FLT/source`. The source file's SHA-256 is
`a750850ebe7c7bc80532fafbc865067df53f9686be9bc7a60d99961c158b4e9b`.
The assertions correspond to scalar comparison at lines 93–100,
general bijectivity at lines 170–223, and left-linear bijectivity at
lines 225–232; their module hypotheses are at lines 28–32 and 102.

Worker 288 retained the scalar-comparison induction and the reduction of
left-linear bijectivity, giving them private helper names within the grouped
proof. The original principal-filter equivalences at lines 104–168 and
direct-limit argument at lines 170–223 are replaced by the full-product
inclusion and output-dependent coordinate-submodule argument described
above. This middle argument is an internal derivation suggested by Worker 98,
not a claim that the original source uses this proof route. It uses the
published `tensorPiComparison_proof` in
`Langlands.LinearAlgebra.RestrictedProduct.TensorPiProof`, whose author and
Imperial source attribution remain in that imported module. No source draft
from that proof is copied here.

The new module uses ordinary Library imports and explicitly names four
independent universes. It needs no new elaborator option, principal-filter
helper, direct-limit helper, or compatibility patch (a)–(d) from the
[finite-adele audit](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2–6 and Appendix B. That audit supplied the source map, not
mathematical acceptance. No Anthropic derivative material is used.

The original copyright, author, and Apache-2.0 notice are retained in the
Lean header, followed by a prominent modification notice. The original
license is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot has no root `NOTICE` file.

## Development checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), incremental check
`62a09407-bccb-4d0c-85ec-8c12e29a79c2` and Lake/declaration inspection
`bddfb367-33a2-4dba-a415-77320683b12e` both succeeded with zero errors and
warnings. Inspection reports kind `theorem`, universe parameters
`uR, uM, uι, uN`, and only the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Private probe
`959fd447-fb8c-4a1b-853c-c6da989409f2` prints the full unapplied theorem
type, the target definition, and the axiom dependencies, and checks the
specialization at four distinct levels `{0, 1, 2, 3}`. It also compiles
without errors or warnings. There are no proof holes or new axioms.
These are development checks; independent semantic acceptance,
exact-target validation, and Integrator publication are separate requirements.
