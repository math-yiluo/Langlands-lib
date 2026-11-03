# Right translations on the coordinate algebra of a unipotent group

Worker 1497.

Internal support for the proof of the Kostant–Rosenlicht theorem
(`Langlands.GroupScheme.UnipotentAffineOrbitClosedStatement`; Milne,
*Algebraic Groups* (2017), Theorem 17.64). The setting is the published
coordinate-algebra interface of `AffineLinearEmbedding`: `F` is a functor from
commutative `k`-algebras to groups, corepresented by `B` through
`e : (F ⋙ forget GrpCat).CorepresentableBy B`, with comultiplication
`comul e`, universal points `pt e`, and coalgebra structure
`(bialgebra e).toCoalgebra`. A `k`-point of the group is a `k`-algebra map
`v : B →ₐ[k] k`. Here `k` is written `CommRingCat.of k`.

## Definitions

- `charTranslate e v : B →ₐ[k] B` is the coordinate map of right translation
  `u ↦ u · g` by the `k`-point `g` classified by `v`: it sends `b` with
  `comul b = ∑ b₁ ⊗ b₂` to `∑ v(b₂) • b₁`. In Lean it is
  `productMap id (ofId ∘ v) ∘ comul e`. This is a derived internal
  construction: it is the standard right-regular action of `G(k)` on
  `O(G)`, written in the given coordinates.
- `charInv e v` is the `k`-point classifying the inverse of the point
  classified by `v`.

## Results

- `pt_comp_charTranslate`: on points with values in any `k`-algebra `A`,
  `pt e (a ∘ charTranslate e v) = pt e a * pt e (ofId ∘ v)`, i.e. the map is
  right multiplication by `g`. Proof: `pt_productMap_comp_comul`.
- `charTranslate_charTranslate_charInv`: right translation by `g` undoes right
  translation by `g⁻¹`. Proof: compute on points with the previous formula and
  use injectivity of `pt e`.
- `charTranslate_eq_rightAct`: `charTranslate e v` is the published comodule
  right action `rightAct v` of `v` viewed as a linear functional (checked on
  pure tensors of `comul e b`).

Assume now `k` algebraically closed, `B` finitely generated and reduced.

- `rightAct_mem_span_charTranslate`: for every linear functional `m` on `B`,
  `rightAct m w` lies in the span of the translates `charTranslate e v w`.
  Proof: otherwise a functional `φ` kills the span but not `rightAct m w`
  (`Submodule.exists_le_ker_of_notMem`). Then the element `leftAct φ w`
  vanishes at every `k`-point `χ`, because
  `χ (leftAct φ w) = φ (rightAct χ w) = φ (charTranslate e χ w) = 0`
  (`apply_leftAct`); by `eq_zero_of_forall_algHom` it is zero, and
  `φ (rightAct m w) = m (leftAct φ w) = 0`, a contradiction.
- `rightAct_mem_of_charTranslate_mem`: hence a subspace `W ⊆ B` stable under
  every `charTranslate e v` is stable under every `rightAct m`.

For a unipotent group (`IsUnipotent (Corepresented.groupScheme F e)`), with
no assumption on `k` beyond being a field:

- `one_mem_of_rightAct_mem`: a nonzero subspace `W ⊆ B` stable under every
  `rightAct m` contains the constant function `1`. This is the step of
  Milne's proof of 17.64 where unipotence gives a nonzero invariant function.
  Proof: pick `f ≠ 0` in `W`; the span `V` of all `rightAct m f` is
  finite-dimensional (`exists_fg_rightAct`), stable (`rightAct_rightAct`),
  contains `f` (`rightAct_counit`) and lies in `W`. A basis `b` of `V` gives
  the matrix `M := Chevalley.subspaceMatrix V b` with
  `comul (b j) = ∑ᵢ b i ⊗ M i j` (`Chevalley.comul_basis`), hence a matrix
  representation `toGLHom e M …`. Unipotence gives a nonzero fixed vector
  `c`; by `UnipotentMatrixCriterion.isFixedVector_iff` and
  `coefficientMatrix_groupSchemeMap`, `∑ⱼ c j • M i j = c i • 1`. Then
  `x := ∑ c i • b i` is nonzero and satisfies
  `x = leftAct ε x = ε(x) • 1` for the counit `ε`, so `ε(x) ≠ 0` and
  `1 = ε(x)⁻¹ • x ∈ V ⊆ W`.
