# The roots of the Chevalley group

Module `Langlands.GroupScheme.SplitExistence.Roots`, namespace
`Langlands.GroupScheme.SplitExistence.ChevalleyData`. Internal helper of the proof of the split
reductive Existence Theorem (task 2132924b). This is the step "the roots of `(G, T)` are the
roots of `P`" (Milne, *Algebraic groups*, proof of Thm. 23.72). The route through the Library's
dynamic subgroups is derived content.

## Declarations

- `gaAffineEquiv A`: affine points of `𝔾ₐ` with values in a `k`-algebra `A`, as `A`.
  `gaCoord_eq_affine` compares it with the global-section coordinate `gaCoord`.
- `affinePointsEquiv_rootToGL`: in affine coordinates, `rootToGL j` sends a point with
  coordinate `s` to `x_j(s)`.
- `epsPoint`: the dual-number point `ε` of `𝔾ₐ`. `epsPoint_mem` says it lies in the Library
  Lie algebra `lieKernel (Gak k) k`, i.e. it reduces to `0` modulo `ε`.
- `ChevGroup.rootLie j`: the Lie algebra element `u_j(ε)` of `G`.
- `ChevGroup.lieMat_rootLie`: its matrix is `e_j(1)`, the first-order term of
  `x_j(ε) = 1 + ε e_j(1)` (`xm_inr`).
- `ChevGroup.isWeightMatrix_eF`: `e_j(1)` is a weight matrix of weight `α_j` (`e_weight`).
- `ChevGroup.roots_t` (`J` finite, `P` reduced, `X` finite free, `G.H` affine and locally of
  finite type): **`roots G.t = range (charOf ∘ P.root)`**. A character is `charOf ξ` for some
  `ξ` (`charEquiv`).
  - If it is a root, `ξ ≠ 0` and its weight space contains a nonzero element. That element has
    a weight matrix of weight `ξ` (`isWeightMatrix_of_mem_weightSpace`), so `ξ` is a root of
    `P` (`exists_root_of_isWeightMatrix`).
  - Conversely `charOf α_j ≠ 0`, since `α_j ≠ 0` and `charEquiv` is injective. Its weight space
    contains `u_j(ε)`, which is nonzero because `e_j(1) ≠ 0` over a field
    (`e_one_map_ne_zero_field`).
