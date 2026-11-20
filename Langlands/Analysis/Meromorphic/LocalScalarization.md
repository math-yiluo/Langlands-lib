# Local reduction of an analytic system to a square system

Module `Langlands.Analysis.Meromorphic.LocalScalarization` proves the local
step of Bernstein–Lapid's proof of the principle of meromorphic continuation.
In a holomorphic frame `ℓ s : ℂⁿ → V`, the system is replaced by `n` chosen
scalar equations. Cramer's rule in adjugate form then gives a numerator `u`
and a denominator `f = det A` for all solutions, both holomorphic. Near a
parameter with a unique solution, some choice of equations has `f ≠ 0`.
Hartogs's theorem enters as the named premise `HartogsDiagonal E` of
`Langlands.Analysis.Meromorphic.WeakComposition`. It is used only for the
holomorphy statements below.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J.
Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, Appendix A
(pp.230–231; TeX `1911.02342.tex` lines 3817–3990). There, near `s₁ ∈ M_unq`,
the system is pulled back by
`ℓ(s) : ℂⁿ → V` and `n` scalar equations `λ ∘ μ_i` are chosen that are
independent at `s₁`, and Cramer's rule is applied. Here the denominator is the
determinant `f` and the numerator is the adjugate solution, so no division
occurs. The identity `f s • x = u s` for every solution `x` is a direct
consequence of `adj A · A = det A · 1`. The source does not single out these
lemmas. Their formulation, for an arbitrary choice of `n` equations, is internal
to the Lean proof.

## Linear algebra

- `clm_apply_eq_sum`: for a continuous complex linear map `L` on `ℂⁿ`,
  `L z = ∑ₖ z k • L (eₖ)`, with `eₖ = Pi.single k 1`.
- `clm_apply_eq_sum_mul`: for a continuous linear form `ψ` and such an `L`,
  `ψ (L z) = ∑ₖ z k * ψ (L eₖ)`.
- `exists_det_ne_zero`: let `r : α → ℂⁿ` be a family of vectors (any index
  type `α`) such that the only `z` with `r a ⬝ᵥ z = 0` for all `a` is `z = 0`.
  Then there are `a : Fin n → α` with `det (r (a j) k)_{j,k} ≠ 0`. Proof: the
  hypothesis forces `span (range r) = ⊤`, because a nonzero linear form
  vanishing on the span would give a nonzero `z`. A linearly independent
  subfamily with the same span (`exists_linearIndependent'`) is then a basis,
  so it has exactly `n` members. Its matrix has linearly independent rows,
  hence is invertible (`Matrix.linearIndependent_rows_iff_isUnit`).

## Holomorphy of algebraic expressions

On a manifold `M` charted on a complex normed space `E` (no manifold axioms
needed here), with `W ⊆ M`:

- `mdifferentiableOn_finset_sum`, `mdifferentiableOn_finset_prod`: finite sums
  and products of scalar functions holomorphic on `W` are holomorphic on `W`
  (induction on the finset).
- `mdifferentiableOn_det`: if all entries of `A : M → Matrix m m ℂ` are
  holomorphic on `W`, so is `s ↦ det (A s)` (Leibniz formula `det_apply'`).
- `mdifferentiableOn_adjugate`: under the same hypothesis every entry of the
  adjugate is holomorphic on `W`. The adjugate entry is the determinant of
  `A` with one row replaced by a constant row (`adjugate_apply`).

## Scalar equations and Cramer's rule

Let `V` be a complex vector space with a topology, `F i` (`i : ι`) complex
vector spaces with topologies, `μ i : M → V →L[ℂ] F i` and `c i : M → F i`, and
`ℓ : M → (ℂⁿ →L[ℂ] V)`. A choice of `n` scalar equations is
`a : Fin n → Σ i, (F i →L[ℂ] ℂ)`; equation `j` is
`(a j).2 (μ (a j).1 s v) = (a j).2 (c (a j).1 s)`. With `eₖ = Pi.single k 1`:

- `scalarMatrix μ ℓ a s` is the `n × n` matrix with entries
  `(a j).2 (μ (a j).1 s (ℓ s eₖ))`. It is the coefficient matrix of these
  equations in the unknown `z` of `v = ℓ s z`.
- `scalarVector c a s` is the vector `j ↦ (a j).2 (c (a j).1 s)`.
- `adjugateSolution μ c ℓ a s = ℓ s (adj A · b)` with
  `A = scalarMatrix μ ℓ a s` and `b = scalarVector c a s`.

`det_smul_eq_adjugateSolution`: if every solution at `s` lies in the range of
`ℓ s`, then `det A • x = adjugateSolution μ c ℓ a s` for every solution `x`
(`x ∈ systemSolutions μ c s`). Proof: write `x = ℓ s z`. Applying the forms
`(a j).2` to the equations `μ (a j).1 s x = c (a j).1 s` and expanding `z` in the
standard basis gives `A *ᵥ z = b`. Hence `adj A *ᵥ b = adj A *ᵥ A *ᵥ z = det A • z`,
and applying `ℓ s` gives the claim. No hypothesis on `M` or on the spaces is
needed.

## Holomorphy on an open set

Let now `M` be charted on a complex normed space `E` with
`IsManifold 𝓘(ℂ, E) 1 M`, and let `hH : HartogsDiagonal E`. Let `(μ, c)` be an
analytic system (`IsAnalyticSystem`). Let `W ⊆ M` be open and `ℓ` a holomorphic
family of operators on `W` (`IsHolomorphicOperatorFamilyOn`). For every choice
`a` of equations:

- `mdifferentiableOn_scalarMatrix`: every entry `s ↦ scalarMatrix μ ℓ a s j k`
  is holomorphic on `W`. It is `s ↦ (a j).2 (μ (a j).1 s (ℓ s eₖ))`, so this is
  `mdifferentiableOn_apply_apply` of `WeakComposition`, applied to the operator
  family `μ (a j).1` and the holomorphic vector function `s ↦ ℓ s eₖ`.
- `mdifferentiableOn_det_scalarMatrix`: `s ↦ det (scalarMatrix μ ℓ a s)` is
  holomorphic on `W`, by `mdifferentiableOn_det`.
- `mdifferentiableOn_adjugate_mulVec`: each coordinate of `adj A(s) *ᵥ b(s)` is
  holomorphic on `W`. It is a finite sum of products of adjugate entries
  (`mdifferentiableOn_adjugate`) and entries of `b`, which are holomorphic
  because `c` is.
- `isHolomorphicOn_adjugateSolution`: `adjugateSolution μ c ℓ a` is
  holomorphic on `W` (weakly), since
  `φ (ℓ s y) = ∑ₖ y k * φ (ℓ s eₖ)` (`clm_apply_eq_sum_mul`).
- `mdifferentiableOn_residual`: for every `i` and every continuous linear form
  `φ` on `F i`, the residual
  `s ↦ φ (μ i s (u s)) - det A(s) * φ (c i s)`, with `u = adjugateSolution μ c ℓ a`,
  is holomorphic on `W`. Its first term is
  `∑ₖ (adj A *ᵥ b)ₖ * φ (μ i s (ℓ s eₖ))`, and `mdifferentiableOn_apply_apply`
  applies again.

## A nonvanishing determinant at a unique solution

`exists_det_scalarMatrix_ne_zero`. Assume each `F i` is Hausdorff and locally
convex over `ℝ` with compatible complex structure, as in the target
statement. Suppose `ℓ s₁` is injective and the system has a unique solution
`v₁` at `s₁` (`s₁ ∈ uniqueSolutionLocus μ c`). Then some choice `a` has
`det (scalarMatrix μ ℓ a s₁) ≠ 0`. This uses no holomorphy and no Hartogs
premise.

Proof. Index all scalar equations by pairs `(i, φ)`, and put
`r (i, φ) = (φ (μ i s₁ (ℓ s₁ eₖ)))ₖ ∈ ℂⁿ`. Suppose `r (i, φ) ⬝ᵥ z = 0` for all pairs.
Then `φ (μ i s₁ (ℓ s₁ z)) = 0` for all `φ`, so `μ i s₁ (ℓ s₁ z) = 0` by
separation in `F i` (`eq_of_forall_clm_apply_eq`). Then `v₁ + ℓ s₁ z` is again a
solution, so `ℓ s₁ z = 0` by uniqueness and `z = 0` by injectivity.
`exists_det_ne_zero` now gives `a` with `det ≠ 0`, and the resulting matrix is
`scalarMatrix μ ℓ a s₁` by definition.
