# The Dixmier–Malliavin theorem on a product with a totally disconnected factor

`Langlands.Analysis.DixmierMalliavin.Product`. The form of the Dixmier–Malliavin theorem used for
adelic groups `G(𝔸) = G(F_∞) × G(𝔸_f)`: on `A × B`, with `A` a Lie group with a closed linear
realization and `B` a locally compact Hausdorff second countable group, for functions smooth in the
first variable and invariant under a compact open subgroup of `B`. Namespace
`Langlands.Analysis.DixmierMalliavin`, except the tensor identity in `Langlands.Hecke`.

## Statements

- `Langlands.Hecke.convolutionIntegral_prod_tensor`: for s-finite `μA`, `μB` and any functions,
  `convolutionIntegral (μA.prod μB) (u ⊗ w) (u' ⊗ w') x = convolutionIntegral μA u u' x.1 *
  convolutionIntegral μB w w' x.2`, where `u ⊗ w = fun p => u p.1 * w p.2`. This is
  `integral_prod_mul` after `(p⁻¹ x).i = pᵢ⁻¹ xᵢ`.
- `exists_eq_sum_slice_mul_cosetIndicator`: for `f : C_c(A × B, ℂ)` with
  `f (x * (1, v)) = f x` for `v` in an open subgroup `V`, there is a finite `T ⊆ B` with
  `f x = ∑ b ∈ T, f (x.1, b) * (b • V).indicator 1 x.2` for all `x`. The cosets `bV` cover the
  compact projection of the support of `f`; finitely many suffice, and `T` takes one representative
  in each of the distinct cosets met, so that at most one term is nonzero and it equals `f x` by the
  right invariance.
- `exists_eq_sum_convolutionIntegral_prod`: for a left Haar measure `μ` on `A × B` (with the product
  of the Borel structures), `f : C_c(A × B, ℂ)` whose slices `a ↦ f (a, b)` are smooth and which is
  right invariant under a compact open subgroup `V`, there are `n` and `φ ψ : Fin n → C_c(A × B, ℂ)`
  with
  - smooth slices `a ↦ φ i (a, b)`, `a ↦ ψ i (a, b)`,
  - right invariance of `φ i` and `ψ i` under `V`,
  - left invariance of `φ i` under some open subgroup `V'` of `B` (here `b V b⁻¹`),
  - left invariance of `ψ i` under `V`,

  and `f x = ∑ i, Hecke.convolutionIntegral μ (φ i) (ψ i) x` for all `x`.

## Proof of the product theorem

Let `μA`, `μB` be Haar measures of the factors; `μ = c (μA × μB)` with `c > 0`
(`isMulLeftInvariant_eq_smul`). Decompose `f = ∑_{b ∈ T} f(·, b) ⊗ 1_{bV}`. Each slice `f(·, b)` is in
`smoothCompactKernels E A`, so `f(·, b) = ∑ φ₀ ⋆ ψ₀` on `A`
(`Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`). On `B`,
`1_{bV} ⋆ 1_V = μB(V) 1_{bV}` (`convolutionIntegral_cosetIndicator`), with `0 < μB(V) < ∞` since `V` is
open and compact. By the tensor identity,
`((c μB(V))⁻¹ φ₀ ⊗ 1_{bV}) ⋆_μ (ψ₀ ⊗ 1_V) = (φ₀ ⋆ ψ₀) ⊗ 1_{bV}`. Summing over the factor pairs and over
`b ∈ T` (the predicate `IsSumConv` is closed under finite sums) gives the theorem. The invariance
properties are those of the coset indicators: `1_{bV}` is right invariant under `V` and left invariant
under `b V b⁻¹`, and `1_V` is invariant on both sides under `V`.

## Literature

J. Dixmier and P. Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), §3, Theorem 3.1, p. 6, for the archimedean
factor; the reduction for adelic groups is standard (the totally disconnected factor only needs the
idempotents `1_V / μ(V)`). The page is that of the English translation *Factorizations of infinitely
differentiable functions and smooth vectors* (typeset in LaTeX, translator not named, paginated
1–24), which does not give the pages of the original. Theorem 3.1 holds for any Lie group and also
controls the supports: the first factor of each term is supported in a given neighbourhood of `e`,
the second in the support of the given function. Here the archimedean factor has a closed linear
realization and no support condition is stated.

## Source and licence

Adapted from `src/GroundTheory/AutomorphicForms/AdelicDixmierMalliavinProduct.lean` of the
repository `leanprover-community/riemann-hypothesis`
(<https://github.com/leanprover-community/riemann-hypothesis>) at commit
`f1f6d65420dbbf36d6cfdac1af8d79511a855a5b`. The repository has no licence file; its text is used
with attribution (see `licenses/RiemannHypothesis/SOURCE.md`).

What is taken and what is changed:

- The coset indicators and their properties (source lines 54–85: `cosetInd`, `cosetInd_apply`,
  `cosetInd_mul`, `isClopen_coset`, `continuous_cosetInd`, `hasCompactSupport_cosetInd`) are taken
  as `cosetIndicator` and its lemmas; `cosetIndicator_mul_left` is new.
- `integral_cosetInd_mul` (lines 202–233) becomes `convolutionIntegral_cosetIndicator`, stated with
  `Langlands.Hecke.convolutionIntegral`.
- The predicate `IsSumConv` and its closure under sums (lines 159–195) are taken, with the source's
  predicate on single functions replaced by the pair predicate `IsFactorPair` and its `C_c`-valued
  convolution `conv` replaced by `Hecke.convolutionIntegral`.
- The decomposition into slices (the step `hdec` of `exists_sum_conv`, lines 352–379) becomes the
  lemma `exists_eq_sum_slice_mul_cosetIndicator`, with a finite set of representatives in `B` instead
  of a finite set of cosets.
- The source works on a group `G` with a chosen `e : G ≃ₜ* A × B`, with `A` a closed subgroup of
  units carrying `IsExpLieAlgebra`, proves the convolution of tensors only for coset indicators
  (`conv_tensorCc_cosetInd`) and carries the Haar scalar through. Here the statement is on `A × B`
  with `A` any Lie group with a closed linear realization, the tensor identity
  `convolutionIntegral_prod_tensor` is general, and the theorem lists the invariance clauses of its
  factors. The source's `ProdSmooth.IsSmooth` and `tensorFun` are not taken; `tensorCc` is restated.
