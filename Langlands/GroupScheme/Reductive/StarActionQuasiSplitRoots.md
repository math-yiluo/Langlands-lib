# Roots of a split torus in a represented regular dynamic parabolic

This internal module supports the proof of `StarActionQuasiSplitStatement`
([`StarActionQuasiSplitProof`](StarActionQuasiSplitProof.md)). It works over every field
`k : Type u`. Its provenance is internal: it combines the published Lie-algebra description
of dynamic parabolics with the weight-space lemmas listed below. The corresponding classical
fact is that the roots of a maximal torus `T` in a Borel subgroup `B = P(ν)` are the roots
positive on `ν`: Milne, *Algebraic Groups* (2022 corrected reprint), source
`milne-2022-algebraic-groups`, Proposition 21.29, printed p.433 (PDF p.444), describes the
Lie algebra of `P(ν)`, for a regular cocharacter `ν` of a split maximal torus, as
`t ⊕ ⊕_{⟨α,ν⟩>0} g_α`.

## Declarations (namespace `Langlands.GroupScheme.StarActionQuasiSplit`)

- `mem_weightSpace_of_targetMapLinear`. Let `b : B ⟶ G` be a homomorphism of group schemes
  over `Spec k` with affine structure maps whose underlying morphism is a monomorphism, and
  `t : T ⟶ B` a homomorphism from a commutative group scheme. If the image of a Lie vector
  `Y` of `B` under `Lie(b)` lies in the weight space of a character `χ` for `t ≫ b`, then `Y`
  lies in the weight space of `χ` for `t`. Proof: the published
  `adjoint_comp_targetMapLinear` and `lieKernelMapLinear_targetMapLinear`
  (`Absolute/RegularCocharacterMaximal`) transport the weight equation through `Lie(b)` over
  every test algebra, and `Lie.targetMapLinear_injective` (`Lie/KernelTargetMaps`) cancels
  `Lie(b)`.
- `mem_roots_iff_of_isRepresentedBy_parabolic`. Hypotheses: `G` additionally locally of finite
  type; `T` split; `b : B ⟶ G` representing the dynamic parabolic `P(ν ≫ t ≫ b)` of a
  cocharacter `ν` of `T`; `ν` regular for `t ≫ b` (`IsRegularCocharacter`: nonzero pairing
  with every root). Conclusion: for every character `α` of `T`,
  `α ∈ roots t ↔ α ∈ roots (t ≫ b) ∧ 0 < ⟨α, ν⟩`.
  - Forward. A nonzero weight vector `Y` of `α` for `t` maps to a nonzero weight vector for
    `t ≫ b` (the published `targetMapLinear_mem_weightSpace`,
    `Absolute/RegularCocharacterMaximal`, and `Lie.targetMapLinear_injective`), so `α` is a
    root of `t ≫ b`. Its image is a dual-number point of the image of `b`
    (`SubgroupFunctor.mem_range`, `SubgroupFunctor`), hence of `P(ν ≫ t ≫ b)`, hence lies
    in the nonnegative weight span of `ν` by the published `dynamicLie` (`Dynamic/LieProof`)
    and `iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan`
    (`Absolute/RegularCocharacterWeights`). If `⟨α, ν⟩ < 0`, the weight space of `α` is
    disjoint from that span (`weightSpace_disjoint_iSup`, `Absolute/RegularCocharacterWeights`),
    a contradiction; regularity excludes `⟨α, ν⟩ = 0`.
  - Backward. A nonzero weight vector `X` of `α` for `t ≫ b`, with `⟨α, ν⟩ > 0`, lies in the
    nonnegative weight span (`nonnegativeWeightSpan_def`,
    `Absolute/RegularCocharacterWeights`), so the published
    `exists_lieKernel_of_mem_nonnegativeWeightSpan` (`Absolute/RegularCocharacterMaximal`,
    applied to `dynamicLie`) gives a Lie vector `Z` of `B` with image `X`. The first lemma
    puts `Z` in the weight space of `α` for `t`, and `Z ≠ 0`.
- `mem_roots_iff_of_isRepresentedBy_parabolic_of_comp`: the same statement for a supplied
  composite `j` with `t ≫ b = j`.

No smoothness, connectedness or reductivity hypothesis is used in this module.
