# Dominance of slice maps from tangent vectors over a field extension

Author: Worker 1630.

This derived helper module generalizes `denseRange_sliceMap` (module
`Lie.AdjointDominance`) from a rational point `(1, t₀)` of `G × 𝔸^e` to a
point `(1, t₀)` with `t₀` over a field extension `K` of `k`. The tangent
computation may then use Lie elements over `K`. The project's route to
unirationality of the scheme of maximal tori (SGA 3, Exposé XIV) needs this
because the regular element of a torus Lie algebra used for the tangent
computation exists only after splitting the torus. The argument repeats the
tangent computation of `AdjointDominance` over `K[ε]` and then applies
`denseRange_of_isTangentSurjectiveAtExtension` (module
`AlgebraicGeometry.TangentSmoothnessExtension`). No external theorem is
asserted.

All declarations live in the namespace `Langlands.GroupScheme.Lie`.
Throughout, `K` is a field extension of a field `k`, both in universe `u`. `G`
is a group scheme over `Spec k`, `n` and `e` are finite types, and `ρ` is a
matrix representation of `G` on `n`. `coefficientSpace e (CommRingCat.of k)` is
the Library's affine space `𝔸^e` over `Spec k`. `sliceMap ρ B` is the
morphism `G × 𝔸^e ⟶ 𝔸^n`, `(g, t) ↦ ρ(g) (B t)`, from `AdjointDominance`.
Matrices and vectors over `k` act on vectors over `K` through
`algebraMap k K`.

- `sliceExtensionPoint t₀` (definition), for `t₀ : e → K`: the
  `K`-valued point `(1, t₀)` of `G × 𝔸^e`, as a morphism over `Spec k` from
  `Spec K`.
- `dualNumberReduction k K` (definition): the morphism `Spec K ⟶ Spec K[ε]`
  over `Spec k` given by `ε ↦ 0`. `dualNumberReduction_left` says that its
  underlying morphism of schemes is the Library's `dualNumberAugmentation K`.
- Private computation lemmas: `appTop_SpecMap_ΓSpecIso_inv` and
  `dualNumberReduction_appTop` evaluate the reduction on global sections
  (the constant part of a dual number). `mulVec_algebraMap_inl_add_inr` and
  `epsilonMatrix_mulVec_inl_add_inr` multiply a matrix over `k` and the
  Library's epsilon matrix `ε M` by a vector `a + ε b` over `K[ε]`.
  `AdjointDominance` has private lemmas with the same three names, which
  cannot be imported. `appTop_SpecMap_ΓSpecIso_inv` repeats its statement
  there. The two matrix lemmas are counterparts of the ones there, which treat
  only vectors over `k`.
- `isTangentSurjectiveAtExtension_sliceMap`: let `G` have affine structure
  morphism, `B : Matrix n e k` and `t₀ : e → K`. Assume every `v : n → K` can
  be written as `ρ(ξ) (B t₀) + B t'` for a Lie element `ξ ∈ lieKernel G K` and
  `t' : e → K`. Then the slice map satisfies
  `IsTangentSurjectiveAtExtension` at the point `sliceExtensionPoint t₀`.

  Proof. Let `t` be a `K[ε]`-point of `𝔸^n` over `k` restricting to the
  image of `(1, t₀)`. Its coordinates `w` have constant part `B t₀`, by the
  formula `coefficientCoordinates_sliceMap` at `(1, t₀)`. Choose `ξ` and
  `t'` for the vector of epsilon parts of `w`. The `K[ε]`-point
  `s = (ξ, t₀ + ε t')` of `G × 𝔸^e` restricts to `(1, t₀)`, since `ξ` lies
  in the kernel of reduction. By `affineCoordinates_sliceMap` and
  `affineMatrix_lieKernel_eq` its image has coordinates
  `(1 + ε ρ(ξ)) B (t₀ + ε t') = B t₀ + ε (ρ(ξ) B t₀ + B t') = w`.
- `denseRange_sliceMap_of_extension`: if moreover `G` is smooth over `k`,
  the slice map has dense range. Proof: `G × 𝔸^e` is smooth over `k` by the
  Library's `smooth_tensor`. `𝔸^n` is locally of finite type and
  geometrically irreducible over `k`. Then
  `denseRange_of_isTangentSurjectiveAtExtension` applies to the point
  `sliceExtensionPoint t₀`, whose composite with the structure morphism is
  `Spec K ⟶ Spec k`.

No hypothesis is placed on the field extension `K`, and irreducibility of `G`
is not assumed. The module proves dominance only; it does not prove
unirationality of any scheme.
