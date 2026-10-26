# Dual Jacquet exponents through source functionals

Author: Worker 23.

This module holds internal helpers for the proof of
`Langlands.GLMaximalConeJacquetQuotientStatement` (task b291a31b). It works
with the published predicate `T.IsDualJacquetExponent B A χ`
(`Langlands.Representation.Exponents.DualJacquet`). That predicate asks that
`χ : (Fin B.length → F^×) →* ℂ^×` has open kernel and that the `χ`-eigenspace
of the split centre on the algebraic dual of the actual normalized opposite
Jacquet module `T.splitCentreOppositeJacquet B A` is nonzero. This module proves
three things:

- that predicate is equivalent to an eigenfunctional condition on the source `A`;
- a dual exponent along `B` gives one along every consecutive coarsening of `B`,
  with the real parts added over each coarse block;
- an irreducible admissible representation has a dual exponent along every
  one-block shape, namely its central character.

These are the standard facts behind Casselman's description of exponents through
the Jacquet module (Casselman 1995, §4), restated for the Library's opposite
normalization. The Lean proofs are direct. Nothing here assumes a published
proposition.

## Coordinate lemmas

- `Subrepresentation.ne_bot_iff_exists`: a subrepresentation is nonzero exactly
  when it contains a nonzero vector.
- In namespace `Langlands.GeneralLinear.BlockShape`:
  - `index_eq_indexEquiv`: `B.index i a = B.indexEquiv ⟨i, a⟩`, by definition.
  - `blockIndex_indexEquiv` (simp):
    `Geometric.blockIndex B (B.indexEquiv ⟨i, a⟩) = i`, the published
    `Geometric.blockIndex_index` restated through `B.indexEquiv`. Here
    `Geometric.blockIndex B x = (B.indexEquiv.symm x).1` is the existing
    block of an ambient coordinate `x`.
  - `mem_oppositeParabolic_iff_blockIndex`: `g` lies in the actual opposite
    parabolic `B.oppositeParabolic R` iff `g x y = 0` whenever
    `Geometric.blockIndex B x < Geometric.blockIndex B y`. Here `x, y : Fin n`
    are ambient coordinates,
    and the published block-index criterion `mem_oppositeParabolic_iff` is
    rewritten through `B.indexEquiv`.
  - `mem_oppositeUnipotentSubgroup_iff_blockIndex`: membership in the actual
    opposite radical `B.oppositeUnipotentSubgroup R` means the condition above
    and, in addition, `g x y = if x = y then 1 else 0` whenever
    `Geometric.blockIndex B x = Geometric.blockIndex B y`.
  - `leviEmbedding_blockScalarLevi_apply`: the embedded block scalar
    `B.leviEmbedding R (B.blockScalarLevi R a)` has entry
    `if x = y then a (Geometric.blockIndex B x) else 0`.

## Consecutive coarsenings

A consecutive coarsening of `B` to `C` is given by a monotone map
`q : Fin B.length → Fin C.length` with
`C.size j = ∑_{q i = j} B.size i` (hypotheses `hq`, `hsize`). These are exactly
the grouping conditions in the target statement. The published
`Langlands.blockIndex_coarsening B C q hq hsize x` gives
`Geometric.blockIndex C x = q (Geometric.blockIndex B x)`.

- `oppositeUnipotentSubgroup_le_of_coarsen R hq hsize`:
  `C.oppositeUnipotentSubgroup R ≤ B.oppositeUnipotentSubgroup R`. If
  `Geometric.blockIndex B x < Geometric.blockIndex B y`, then either `q`
  separates the two blocks
  strictly, so the `C`-condition gives zero, or they lie in the same `C`-block,
  so `x ≠ y` and the `C`-diagonal-block condition gives zero.
- `leviEmbedding_blockScalarLevi_coarsen R hq hsize a`: the `B`-block scalar
  with entries `a ∘ q` and the `C`-block scalar with entries `a` are the same
  ambient matrix. Compare entries with the previous lemma.
- `MaximalConePolygon.prod_pairs_coarsen`: in a commutative group,
  `∏_{i < i'} (w (q i)^(b i))^(b i') / (w (q i')^(b i'))^(b i)` equals the same
  product over coarse indices with sizes `c`, provided `c j = ∑_{q i = j} b i`.
  Each factor is `(w (q i) / w (q i'))^(b i * b i')`. Since `q` is monotone,
  the condition `i < i'` may be replaced by `q i < q i'`: pairs with `i < i'`
  and `q i = q i'` contribute `1`, and `q i < q i'` forces `i < i'`. The
  product is then grouped
  along the fibres of `q` (`Finset.prod_fiberwise`), and
  `∑_{q i = j} ∑_{q i' = j'} b i * b i' = c j * c j'`.

## The source criterion

`isDualJacquetExponent_iff B A χ`: `T.IsDualJacquetExponent B A χ` holds iff
`χ` has open kernel and some nonzero `ℓ : Module.Dual ℂ A` satisfies

- `ℓ (A.ρ g v) = ℓ v` for all `g` in the actual opposite radical
  `B.oppositeUnipotentSubgroup F.Carrier`, and
- `ℓ (A.ρ (leviEmbedding (blockScalarLevi a)) v) = (δ_B^{1/2}(a))⁻¹ · χ a · ℓ v`
  for all `a : Fin B.length → F^×`. Here `δ_B^{1/2}` is the published
  `T.leviHalfModulus B` evaluated at the block scalar.

Forward direction: compose an eigenfunctional `φ` with the surjection
`T.splitCentreOppositeJacquetMk B A`. Invariance follows from
`Jacquet.mk_apply_subgroup`, and the eigen-equation is the published
`mem_dualJacquet_eigenspace_iff`. Backward direction: descend `ℓ` through
`Jacquet.lift`, then apply the same eigenspace criterion. Nonvanishing transfers
in both directions because the quotient map is surjective.

## Restriction to a coarsening

- `leviModulus_blockScalarLevi_coarsen hq hsize a`: the full modulus
  `T.leviModulus B` at the `B`-block scalar `a ∘ q` equals `T.leviModulus C` at
  the `C`-block scalar `a`. The published `leviModulus_apply` and
  `determinantNorm_scalar` reduce both sides to the pair products above, with
  `w j = T.normalizedAbsUnits (a j)`.
- `isDualJacquetExponent_coarsen hq hsize h hχC`: if `χ` is a dual exponent
  along `B` and `χC a = χ (a ∘ q)` for all `a`, then `χC` is a dual exponent
  along `C`. The same source functional works. It is invariant under the smaller
  radical `N̄_C ≤ N̄_B`. On `C`-block scalars, the embedding lemma and the modulus
  identity turn the `B`-eigen-equation into the `C`-eigen-equation. The kernel of
  `χC` is the preimage of the kernel of `χ` under the continuous map
  `a ↦ a ∘ q`.
- `isRealPartOf_coarsen hr hχC s hs`: if `r` is a real part of `χ`
  (`T.IsRealPartOf χ r`, `Langlands.Representation.Exponents.Jacquet`) and
  `s j = ∑_{q i = j} r i`, then `s` is a real part of `χC`. Group the product
  `∏_i |a (q i)|^(r i)` along the fibres of `q` and use
  `Real.rpow_sum_of_pos`.

## One block

`exists_isDualJacquetExponent_of_length_eq_one hB hi ha`: if `B.length = 1`,
`A.ρ` is irreducible and `A.ρ` is admissible for `T.topology`, then some `χ`
is a dual exponent of `A` along `B`.

- The published `admissibleSchur_centralCharacter`
  (`Langlands.Representation.Smooth.Schur.Proof`) gives `ω` on the centre with
  `A.ρ z v = ω z • v`. Put `χ a = ω (scalarToCenter (a i₀))`, where `i₀` is the
  only block index.
- Every ambient coordinate lies in block `i₀`. So the embedded block scalar is
  the ambient scalar matrix `scalar (a i₀)`, the opposite radical is trivial
  (every `g` in it has identity entries), and the modulus is an empty product.
  Its half is therefore `1`.
- `A` is nontrivial because its group-algebra module is simple. Choose `v ≠ 0`,
  then a functional `ℓ` with `ℓ v ≠ 0` (`Module.Projective.exists_dual_ne_zero`).
  This `ℓ` satisfies the source criterion.
- The kernel of `χ` is open. It contains the preimage of an open subgroup `K`
  fixing `v` under the continuous map `a ↦ scalar (a i₀)`
  (`GeneralLinear.scalarContinuous`). Indeed, for such `a`,
  `χ a • v = A.ρ (scalar (a i₀)) v = v`, so `χ a = 1`.

## Sources

Casselman, *Introduction to the theory of admissible representations of p-adic
reductive groups* (draft of 1 May 1995), §3–4: Jacquet modules, central
exponents, and their behaviour under passage to larger parabolics. The Lean
statements here are internal helpers tied to the Library's opposite
normalization. They are proved directly and are not transcriptions of a
numbered source result.
