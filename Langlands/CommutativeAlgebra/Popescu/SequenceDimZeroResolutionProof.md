# Proof: the sequence form of Stacks Lemmas 9.2 and 9.4

`Langlands.CommutativeAlgebra.Popescu.sequenceDimZeroResolution` proves
`SequenceDimZeroResolutionStatement.{u}` for every universe `u`. It is the reduction
`sequenceDimZeroResolution_of` applied to two published Library proofs:

- `Desing.strictlyStandardDesingularization`, which proves
  `StrictlyStandardDesingularizationStatement` (Stacks Lemma 7.3, Tag 07F0), from module
  `StrictlyStandardDesingularizationProof`;
- `localDimZeroResolution`, which proves `LocalDimZeroResolutionStatement` (Lemmas 9.3
  and 9.4, Tags 07F9 and 07FA), from module `LocalDimZeroResolutionProof`.

The source is Stacks Project, *Smoothing Ring Maps*, Lemma 9.2 (Tag 07F8). The bottom
problem is resolved as in steps (18) and (20) of the proof of Lemma 11.4 (Tag 07FJ).

## The reduction `sequenceDimZeroResolution_of`

`sequenceDimZeroResolution_of (h6 : StrictlyStandardDesingularizationStatement)
(h2 : LocalDimZeroResolutionStatement) : SequenceDimZeroResolutionStatement` is the
induction of Lemma 9.2. It follows `canBeResolved_of_sequence` in the Library module
`LocalLifting` (the induction for Lemma 10.3), with a different bottom hypothesis.

`SequenceDimZero.Bottom R A Λ f q K` is the bottom hypothesis of the statement for the
ideal `K = (πᵢ⁸)`:

- quantify over all quotient models `σ : R → R₁` and `τ : Λ → Λ₁` of `R/K → Λ/KΛ`, and
  over all primes `Q` over `q`;
- require that `Q` is a minimal prime;
- require that `A → Λ₁ → (Λ₁)_Q` factors through a smooth algebra `T` over the
  localization of `R₁` at `Q ∩ R₁`.

`SequenceDimZero.resolve` proves the statement by induction on the length `r`.

**Base case `r = 0`.** Take `σ = id` and `τ = id` with `Q = q`. This gives the hypotheses
of `LocalDimZeroResolutionStatement`. If `h_A ⊄ q`, the identity of `A` already resolves
the problem.

**Inductive step.**
- The one-step lifting `canBeResolved_of_quot` from `LocalLifting` (Lemma 7.3 applied to
  `π₀`) reduces the problem to the quotient problem over `R/π₀⁸`, for the algebra
  `(R/π₀⁸) ⊗ A`, for `Λ/π₀⁸Λ` and for the images of `π₁, …, π_{r−1}`.
- The induction hypothesis applies to the quotient problem. The annihilator conditions
  and strict standardness transfer as in `canBeResolved_of_sequence`, using
  `comap_mk_map_mk`, `span_image_lt_succ`, `algebraMap_quot_tensor` and
  `IsStrictlyStandard.baseChange` from `LocalLifting`.
- **The bottom hypothesis transfers by composing surjections.** Given quotient models
  `σ`, `τ` of the quotient problem, the original bottom hypothesis is applied to
  `σ ∘ mk` and `τ ∘ mk`. It provides `u : A → T`. This extends to
  `u' : (R/π₀⁸) ⊗ A → T` by `Algebra.TensorProduct.lift`, with `T` an `R`-algebra
  through `R → R₁ → (R₁)_𝔭 → T`.
  - `u'` restricts on `R/π₀⁸` to the structure map.
  - `v ∘ u'` agrees with the reduced map on pure tensors, using `f.commutes`.

## Final theorem

`sequenceDimZeroResolution` is
`sequenceDimZeroResolution_of Desing.strictlyStandardDesingularization localDimZeroResolution`.
Its type is exactly `SequenceDimZeroResolutionStatement.{u}`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
