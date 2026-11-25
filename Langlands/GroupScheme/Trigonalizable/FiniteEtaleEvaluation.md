# Evaluation and descent for finite étale algebras

Module
`Langlands.GroupScheme.Trigonalizable.FiniteEtaleEvaluation`.

Let `A` be an étale algebra over the field `k`, and `L/k` a separably
closed extension field (that is, `L` is separably closed). Write `X` for
`A →ₐ[k] L`. The equivalence `EtaleExtensionSplit.evaluationEquiv` identifies
`L ⊗[k] A` with the algebra of `L`-valued functions on `X`. It uses
Mathlib's product decomposition of an étale algebra over a separably
closed field, the indexing of spectrum points by algebra maps into `L`,
and the tensor-product adjunction. Its coordinate at `x ∈ X` sends
`l ⊗ a` to `l * x(a)`. Since `A` injects into the scalar extension, equality
of elements of `A` can be tested by every `x ∈ X`
(`eq_of_geometric_evaluation`).

When `L/k` is Galois, `exists_algHom_of_equivariant` descends a family
`F : X → (B →ₐ[k] L)` satisfying `F(σ ∘ x) = σ ∘ F(x)` to a map
`g : B →ₐ[k] A` with `x ∘ g = F(x)` for every `x`. To descend each
coordinate `b ∈ B`, take the tensor corresponding to `x ↦ F(x)(b)`.
Evaluation of the tensor transformed by `σ ⊗ id` at `x` is the result of
applying `σ` to evaluation at `σ⁻¹ ∘ x`. Thus the tensor is fixed by all
`σ`. Expand it in the base change of a `k`-basis of `A`; each coefficient
is fixed and comes from `k` by `InfiniteGalois.mem_range_algebraMap_iff_fixed`.
Finiteness of the basis gives an element of `A` with those coefficients.
The algebra laws for `g` follow by evaluation at every `x`, where they
are the laws for `F(x)`. There is no finite-degree assumption on `L/k`,
nor any étaleness assumption on `B`.

These are derived coefficient-algebra lemmas for
[descent of morphisms from finite étale schemes](FiniteEtaleMorphisms.md).
The proof uses Mathlib's finite étale and Galois fixed-field results; it is
not a separate assertion about group-scheme extensions from SGA 3.
