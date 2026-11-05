# Nonzero weights on the Lie algebra are roots

Module `Langlands.GroupScheme.SplitExistence.RootBound`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). The argument is the dynamic method: the Lie algebra
of `G` is graded by the weights of the regular cocharacter `λ`, the positive part is the Lie
algebra of `U_G(λ)`, and the zero part is the Lie algebra of `Z_G(λ)` (Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, Prop. 2.1.8, available through the Library's `dynamicLie`). The bound
on weights is derived content.

## Declarations

- `exists_root_of_mem_span` (any field `F`): if a nonzero matrix `N` is a weight matrix of
  weight `ξ` and lies in the span of the root matrices `e_j(1)`, `j ∈ S`, then `ξ = α_j` for
  some `j ∈ S`. The proof uses the linear projection that keeps the entries `(c, d)` with
  `wt c - wt d = ξ`. It fixes `N`. If `ξ` were not a root in `S`, it would kill every `e_j(1)`,
  `j ∈ S`, because their entries shift weights by `α_j` (`e_weight`). Then it would kill `N`.
- `ChevGroup.exists_root_of_pos` (`P` reduced, `J` finite, `G.H` affine and locally of finite
  type): if a nonzero Lie algebra element `x` has a weight matrix of weight `ξ` with
  `ℓ(ξ) > 0`, then `ξ` is a root. By `mem_weightSpace_cochar`, `x` has `λ`-weight `ℓ(ξ) > 0`.
  So the Library's `dynamicLie` places it in the Lie algebra of `U_G(λ)`. Its matrix then lies
  in the span of the `e_γ(1)` with `γ > 0` (`coefficients_mem_span_of_unipotent`, module
  `UnipotentLie`), and `exists_root_of_mem_span` applies.
- `ChevGroup.exists_root_of_isWeightMatrix` (`J` finite, `P` reduced, `X` finitely generated):
  every nonzero Lie algebra element whose matrix is a weight matrix of a nonzero weight `ξ`
  has `ξ` a root. There are three cases.
  - `ℓ(ξ) > 0`: the previous lemma.
  - `ℓ(ξ) < 0`: the previous lemma for the opposite Chevalley group `G.neg`, whose functional
    is `-ℓ`.
  - `ℓ(ξ) = 0`: `x` lies in the Lie algebra of `Z_G(λ)`, which is contained in the torus
    (`centralizer_le`). So the matrix of the dual-number point `x` is diagonal. A weight matrix
    of nonzero weight has zero diagonal, hence `x = 0`, a contradiction.
