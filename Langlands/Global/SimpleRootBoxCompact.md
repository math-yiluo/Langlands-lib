# Compact simple-root boxes in the positive torus

Author: Worker 1179. Part of task 40747bb3 (finite volume of `G(F) \ G(𝔸_F)¹`), with
Worker 235.

This module proves `SimpleRootBoxCompactStatement`
(`Langlands/Global/AdelicSiegelMeasureReduction.lean`) from two existing Library
propositions about relative roots:

- `RelativeRootNegationStatement`
  (`Langlands/GroupScheme/Rational/RelativeRootNegationStatement.lean`): the relative roots of
  a maximal split torus of a connected reductive group are stable under negation;
- `RelativeCharacterRootComplementStatement`
  (`Langlands/GroupScheme/Rational/RelativeCentralDirectionsStatement.lean`): in
  `X*(T) ⊗ ℚ`, the span of the relative roots and the restrictions of the rational characters
  of `G` are complementary subspaces.

The main theorem is `simpleRootBoxCompactStatement_of_rootComplement`. The proof has an
algebraic step and an analytic step, explained below. Neither input proposition is proved
here, so `SimpleRootBoxCompactStatement` remains conditional on them.

Notation is as in `AdelicSiegelMeasureReduction.md`:

- `Δ = simpleRelativeRoots i ν`;
- `A_{T} = PositiveRealTorus.intrinsicSubgroup F T` is the positive torus;
- `|χ|(x) = PositiveRealTorus.normCharacter F T χ x` is the normalized idelic norm of a
  character `χ` at `x`.

## Rational extension

The section is generic: `M` is any abelian group.

- `ratExtend ℓ`: for an additive map `ℓ : M → ℝ`, the additive map `ℚ ⊗[ℤ] M → ℝ` with
  `q ⊗ m ↦ q ℓ(m)`. It is built with `TensorProduct.lift`. `ratExtend_toRat` says it extends
  `ℓ`.
- `exists_abs_le_of_toRat_mem_ratSpan`: suppose `1 ⊗ c` lies in the rational span of
  `S ⊆ M`. Then there is `C ≥ 0`, depending only on `c` and `S`, with the following
  property: for every additive `ℓ : M → ℝ` and every `B` with `|ℓ(χ)| ≤ B` for all `χ ∈ S`,
  one has `|ℓ(c)| ≤ C B`. *Proof.* Write `1 ⊗ c = Σ_k f_k (1 ⊗ χ_k)` with `f_k ∈ ℚ` and
  `χ_k ∈ S` (`Submodule.mem_span_set'`). Apply `ratExtend ℓ`, which is `ℚ`-linear by
  Mathlib's `map_rat_smul`. This gives `ℓ(c) = Σ_k f_k ℓ(χ_k)`, so `C = Σ_k |f_k|` works.

## Compact boxes in `ℝ≥0ˣ` and in the positive torus

- `isCompact_unitsBox a b ha`: for `a > 0`, the set of `u ∈ ℝ≥0ˣ` with `a ≤ u ≤ b` is
  compact. *Proof.* The corresponding set of `ℝ≥0` is closed and contained in a compact
  interval, so it is compact. It consists of nonzero elements, so it lies in the image of
  `Units.val`, which is an embedding (`Units.isEmbedding_val₀`). Compactness then passes to
  the preimage (`IsInducing.isCompact_preimage_iff`).
- `logNormHom F T x`: for a point `x` of `T(𝔸_F)`, the map `χ ↦ log |χ|(x)`. It is additive
  in `χ`, because character values multiply (`characterValue_add'`) and the idelic norm is
  multiplicative.
- `abs_log_le_of_mem_Icc`: if `v ≠ 0` and `s⁻¹ ≤ v ≤ s` in `ℝ≥0`, then
  `|log v| ≤ |log s|`.
- `isCompact_characterBox`: let `T` be a split torus and `S` a set of characters whose
  rational span is all of `X*(T) ⊗ ℚ`. Then for every `s : ℝ≥0` the box
  `{x ∈ A_T | ∀ χ ∈ S, s⁻¹ ≤ |χ|(x) ≤ s}` is compact. *Proof.*
  - Choose a splitting `T ≅ 𝔾_m^I`. The Library map `fullIntrinsic : (ℝ≥0ˣ)^I → A_T` is
    continuous (from `isClosedEmbedding_full`) and surjective (`fullIntrinsic_surjective`).
    So it suffices to show that the preimage of the box is compact.
  - The preimage is closed, because the box is cut out by continuous inequalities.
  - It remains to show that the preimage lies in a product of compact boxes
    `exp(-b_i) ≤ x_i ≤ exp(b_i)`. Fix a coordinate `i` and apply the previous lemma to the
    coordinate character `c_i` and to `ℓ = logNormHom` at `fullIntrinsic x`, with
    `B = |log s|`. This gives `|ℓ(c_i)| ≤ C_i |log s|`.
  - The value `|c_i|(fullIntrinsic x)` equals `x_i^d` with `d = [F : ℚ]`. This follows from
    `absoluteValue_characterValue_full`, together with the fact that the positive monomial of
    `c_i` is the `i`-th coordinate (from `characterValue_coordinateCharacter`,
    `characterValue_full`, `coordinates_full` and injectivity of `PositiveRealIdeles.full`).
    Hence `d |log x_i| ≤ C_i |log s|`, and one may take `b_i = C_i |log s| / d`.

## The spanning step

`ratSpan_restrict_simpleRelativeRoots_eq_top` proves the following. Assume the two input
propositions and an actual algebraic Siegel setup `(T, i, ν, T₀, j)` for a connected
reductive `G` over a number field. Then the rational span of the restricted simple roots
`j ≫ α` (`α ∈ Δ`) is all of `X*(T₀) ⊗ ℚ`.

*Proof.* Let `ρ : X*(T) ⊗ ℚ → X*(T₀) ⊗ ℚ` be restriction along `j`.

1. `ρ` is surjective (`IsSplitTorus.rationalCharacterRestrictRat_surjective_of_mono`). This
   needs `j` to be a monomorphism. Since `j ≫ i = t₀ ≫ d` is a composite of two closed
   immersions (the maximal split torus `t₀` of the derived group and the derived subgroup
   `d`), it is a monomorphism, and so is `j`.
2. `ρ` kills the restrictions of rational characters of `G`. The range of `j ≫ i` lies in
   the derived subgroup. So every rational character of `G` is trivial along `j ≫ i`
   (`charactersTrivialAlong_of_range_le_derived`), and restriction is functorial
   (`characterRestrict_comp`).
3. Because `ν` is generic and the roots are stable under negation, the simple roots span the
   root span (`ratSpan_simpleRelativeRoots_eq_relativeRootSpan`).
4. By the complement statement, every `x ∈ X*(T) ⊗ ℚ` is `a + b` with `a` in the root span
   and `b` a restricted character of `G`. Then `ρ(x) = ρ(a)`. So the image under `ρ` of the
   span of `Δ`, which is the span of the restricted simple roots, is everything.

## The theorem

`simpleRootBoxCompactStatement_of_rootComplement hneg hcompl` combines the spanning step,
applied to the set `S` of restricted simple roots, with `isCompact_characterBox` for the
split torus `T₀`. `T₀` is split because it is a maximal split torus of the derived group. The
box in `SimpleRootBoxCompactStatement` is indexed by `α ∈ Δ` and uses `|j ≫ α|`. This is the
box of `isCompact_characterBox` for the image set `S`, by `Set.forall_mem_image`.

This is the argument sketched in the provenance of `SimpleRootBoxCompactStatement` in
`AdelicSiegelMeasureReduction.md`. There the spanning fact was justified from Borel–Tits,
Théorème 5.3. Here it is derived from the two Library propositions instead.
