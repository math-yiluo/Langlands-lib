# Central elements act by scalars on a lowest-weight functional

Lean module: `Langlands.Representation.Archimedean.JacquetFunctionalCenter`, namespace
`Langlands.Archimedean.JacquetCenter`.

This module holds no statement definition. It proves one general algebraic lemma, the core of
Harish-Chandra's computation of the infinitesimal character of a principal series. Its consumer
is `ComplexPrincipalSeriesInfinitesimalCharacter`.

## Setting

- `L` is a complex Lie algebra and `π : L →ₗ⁅ℂ⁆ Module.End ℂ V` is a representation.
- `envelopingAction π : U(L) →ₐ[ℂ] Module.End ℂ V` is its extension to the universal
  enveloping algebra (Library, `RealGenericLargeReduction`).
- `ℓ : V →ₗ[ℂ] ℂ` is a linear functional and `N : Set L` is a set of "lowering" elements.

## Main result

`exists_comp_envelopingAction_eq_smul`. Assume:

1. `hH`: some `H ∈ L` acts on `ℓ` by a scalar, `ℓ ∘ π(H) = μ ℓ`;
2. `hN`: every `y ∈ N` satisfies `⁅H, y⁆ = -(k • y)` for some natural number `k > 0`;
3. `hdec`: for every `x ∈ L` there are `c ∈ ℂ` and `y ∈ span N` with
   `ℓ ∘ π(x) = c ℓ + ℓ ∘ π(y)`.

Then every `z` in the center of `U(L)` satisfies `ℓ ∘ π(z) = c ℓ` for some `c ∈ ℂ`.

## Definitions and auxiliary results

- `wordProd w`: the product `ι y₁ ⋯ ι y_k` in `U(L)` of a list `w = [y₁, …, y_k]` of elements
  of `L`. Lemmas: `wordProd_nil`, `wordProd_append_singleton`.
- `envelopingAction_ι` (`envelopingAction π (ι x) = π x`) and `comp_envelopingAction_mul`
  (`ℓ ∘ π(a b) = (ℓ ∘ π(a)) ∘ π(b)`).
- `nbarSpan π ℓ N`: the span of the functionals `ℓ ∘ π(wordProd w)` over the words `w` with
  letters in `N`. The empty word contributes `ℓ` (`self_mem_nbarSpan`). Appending a letter of `N`
  stays inside the span (`comp_mem_nbarSpan`), and so does `ℓ ∘ π(y)` for `y ∈ span N`
  (`comp_span_mem_nbarSpan`).
- `scalarSubmodule π ℓ`: the subspace of `x ∈ L` with `ℓ ∘ π(x) ∈ ℂ ℓ`.
- `decSubmodule π ℓ N`: the subspace of `x ∈ L` satisfying the conclusion of `hdec`.
  `scalarSubmodule_le_decSubmodule` and `subset_decSubmodule` show that it contains
  `scalarSubmodule` and `N`. With these, `hdec` can be checked on a spanning set.
- `word_comp_mem_nbarSpan`, `comp_lie_mem_nbarSpan`, `comp_envelopingAction_mem_nbarSpan`:
  under `hdec`, `nbarSpan` is stable under every `π(x)` and so under all of `U(L)`. In
  particular it contains `ℓ ∘ π(u)` for every `u ∈ U(L)`. The first of these is proved by
  induction on the word, using `π(y) π(x) = π(x) π(y) + π⁅y, x⁆`. The last uses the Library's
  induction principle `InfinitesimalCharacter.envInduction` for `U(L)`.
- `exists_mul_wordProd`: under `hN`, each word `w` in `N` satisfies
  `ι H · wordProd w = wordProd w · ι H - k • wordProd w` for some natural `k`, with `k > 0`
  if `w` is nonempty.

## Proof of the main result

Let `T φ = φ ∘ π(H) - μ φ` on `V →ₗ[ℂ] ℂ`. By `exists_mul_wordProd`, `T` acts on
`ℓ ∘ π(wordProd w)` by multiplication by `k ≠ 0` for each nonempty word `w`. Hence
`nbarSpan ≤ ℂ ℓ ⊔ B`, where `B` is the span of the eigenspaces of `T` for nonzero eigenvalues.
Write `ℓ ∘ π(z) = c ℓ + b` with `b ∈ B`. Since `z` commutes with `ι H`,
`T (ℓ ∘ π(z)) = 0`, and `T ℓ = 0` by `hH`. So `T b = 0`, that is, `b` lies in the
`0`-eigenspace. Eigenspaces for distinct eigenvalues are independent (Mathlib
`Module.End.eigenspaces_iSupIndep`), so `b = 0`.

## Provenance

This is an internal lemma. The argument is the standard one behind Harish-Chandra's theorem
that a principal series has an infinitesimal character. There `ℓ` is evaluation at the
identity, `N` spans the opposite nilradical, and the elements acting on `ℓ` by scalars span the
Borel subalgebra. Here it is formulated and proved without a Poincaré–Birkhoff–Witt basis.
