# Ordering the Jacquet exponents of `(𝔤𝔩_2(ℂ), U(2))`-modules

Lean module: `Langlands.Representation.Archimedean.ComplexGLTwoJacquetOrdering`
(namespace `Langlands.Archimedean`, universe `uV` for the module carrier). The module imports
`Langlands.Representation.Archimedean.ComplexJacquetReduction` and contains only the
proposition `ComplexGLTwoJacquetOrderingStatement`. Nothing is proved here.

## Statement

`ComplexGLTwoJacquetOrderingStatement` says the following for every `V : Type uV` with
`[AddCommGroup V] [Module ℂ V]`, every `ρ : Representation ℂ (Matrix.unitaryGroup (Fin 2) ℂ) V`
and every complex Lie algebra map `π : ℂ ⊗[ℝ] 𝔤𝔩_2(ℂ) → End_ℂ V`:

Assume `(ρ, π)` is a `(𝔤𝔩_2(ℂ), U(2))`-module (`IsComplexGKModule 2 ρ π`). Let `ℓ : V →ₗ[ℂ] ℂ`
be nonzero, and let `a b : Fin 2 → ℂ` satisfy `IsComplexJacquetFunctional 2 π ℓ a b`. That is,

* `ℓ (π (1 ⊗ X) v) = 0` for every strictly upper triangular `X` and every `v` (here `X` is a
  complex multiple of `E_01`);
* `ℓ ∘ π (1 ⊗ E_jj) = a_j ℓ` and `ℓ ∘ π (1 ⊗ i E_jj) = b_j ℓ` for `j = 0, 1`.

Then there are `ℓ' : V →ₗ[ℂ] ℂ` and `a' b' : Fin 2 → ℂ` with

* `ℓ' ≠ 0` and `IsComplexJacquetFunctional 2 π ℓ' a' b'`;
* `a'_0 + a'_1 = a_0 + a_1`;
* `Re a'_0 ≤ Re a'_1 + 2`.

The statement assumes no irreducibility (`IsIrreducibleGKModule`), no admissibility
(`IsAdmissibleGKModule`) and no finite generation. Nothing is required of `b'`. If `ℓ` is
already ordered (`Re a_0 ≤ Re a_1 + 2`), then `ℓ' = ℓ` works.

### Normalization

With the normalization of `ComplexJacquetReduction`, `a_j = 2 t_j + (n - 1) - 2 j`, which for
`n = 2` is `a_0 = 2 t_0 + 1` and `a_1 = 2 t_1 - 1`. The condition `Re a'_0 ≤ Re a'_1 + 2` then
reads `Re t'_0 ≤ Re t'_1`. This is the closed antidominant chamber of
`ComplexOrderedJacquetFunctionalStatement`. The condition `a'_0 + a'_1 = a_0 + a_1` says that
`t'_0 + t'_1 = t_0 + t_1`, so the new functional has the same eigenvalue on `π (1 ⊗ I)` as the old
one.

## Role

The intended use is in the rank-one statement `ComplexJacquetRankOneStatement` (B) of
`ComplexJacquetReduction`, for general `n`. Let `ℓ` be a Jacquet functional of a
`(𝔤𝔩_n(ℂ), U(n))`-module `V` with exponents `a`, `b`, and let `j = i + 1`. Write `S` for the
subspace spanned by the following vectors:

* `π (1 ⊗ X) v`, for strictly upper triangular `X` with `X_ij = 0`;
* `(π (1 ⊗ E_kk) - a_k) v` and `(π (1 ⊗ i E_kk) - b_k) v`, for `k ∉ {i, j}`.

The quotient `V / S` is a `(𝔤𝔩_2(ℂ), U(2))`-module through the block embeddings at rows and
columns `i, j`, and `ℓ` factors through it. This statement, applied to `V / S`, then gives (B).
Because no irreducibility or admissibility is assumed here, the reduction does not need
admissibility of `V / 𝔫_P V` (Wallach 1979, 4.20). That reduction is a separate artifact.

## Why it is expected to hold

The proof is left to a separate task. The expected route is as follows.

1. Frobenius reciprocity (`ComplexJacquetFrobeniusStatement` in
   `ComplexJacquetFrobenius`, which also assumes no irreducibility or admissibility) gives a
   nonzero `(𝔤𝔩_2(ℂ), U(2))`-map `B` from `V` into the `U(2)`-finite vectors of a principal
   series `I(d_0, d_1)` of `GL_2(ℂ)`. Its exponents satisfy `a_j = 2 t_j + 1 - 2 j`.
2. The image `B(V)` is a nonzero submodule of the `U(2)`-finite principal series. That module has
   finite length (Wallach 1979, §7 and 8.8–8.12, where the principal series of `GL(2, ℂ)` and its
   irreducible constituents are described). So `B(V)` has an irreducible quotient `Q`.
3. `Q` is an irreducible admissible `(𝔤𝔩_2(ℂ), U(2))`-module. By the subrepresentation form of the
   Langlands classification for `GL_2(ℂ)` (Wallach 5.13 and 6.7 for `n = 2`; also 8.8–8.12), `Q`
   embeds into a principal series `I(d'_0, d'_1)` with `Re t'_0 ≤ Re t'_1`. Evaluation at the
   identity then gives a nonzero Jacquet functional `λ` on `Q` with exponents
   `a'_j = 2 t'_j + 1 - 2 j`, so `Re a'_0 ≤ Re a'_1 + 2`.
4. Set `ℓ' = λ ∘ (B(V) → Q) ∘ B`. It is nonzero, and it is a Jacquet functional with exponents
   `a'`, `b'`, since every map in the composite intertwines `π`.
5. The centre of `𝔤𝔩_2(ℂ) ⊗_ℝ ℂ`, spanned by `1 ⊗ I` and `1 ⊗ i I`, acts on `I(d_0, d_1)` by
   scalars, and `1 ⊗ I` acts by `2 t_0 + 2 t_1 = a_0 + a_1`. Evaluating `ℓ' ∘ π (1 ⊗ I)` in two
   ways gives `a'_0 + a'_1 = a_0 + a_1`.

## Provenance

Derived. The statement does not appear in this form in the literature. It is the `GL_2(ℂ)` case of
the ordered Jacquet functional statement (`ComplexOrderedJacquetFunctionalStatement` at `n = 2`,
which comes from Wallach 1979, 4.16–4.18, 5.13 and 6.7). It is modified in two ways:

* the irreducibility and admissibility hypotheses are dropped, which is justified by Frobenius
  reciprocity and the finite length of the `GL_2(ℂ)` principal series, as sketched above;
* the eigenvalue of the centre is kept, `a'_0 + a'_1 = a_0 + a_1`.

It is the `GL_2` input for the adjacent case of the minimality argument in the proof of
Wallach 1979, Lemma 5.13 (printed p. 79), replacing the parabolic Jacquet module of 4.20–4.21 and
5.3 (printed p. 78) by the quotient `V / S` above. The principal series of `GL(2, ℂ)` is treated
in Wallach 1979, §7 (printed pp. 80–82) and 8.8–8.12 (printed pp. 84–85); printed page = PDF
page − 3.
