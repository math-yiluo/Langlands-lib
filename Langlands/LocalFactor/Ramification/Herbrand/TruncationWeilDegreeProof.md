# Truncation preserves the Weil degree

`Langlands.Ramification.Kummer.truncationWeilDegree` proves
`TruncationWeilDegreeStatement.{u}` at an arbitrary universe level `u`. Let
`F` be a p-adic field, `E` a finite intermediate extension and `μ ≥ 0` with
`E.field.fixingSubgroup ⊔ G_F^μ = ⊤`. Then the map
`intermediateWeilMap F E : W_E → W_F` preserves the geometric degree: for every
`w` in the Weil group of `E.asPadicField`,
`localDegree F (intermediateWeilMap F E w) = localDegree (E.asPadicField) w`.

## Auxiliary lemma

`extensionResidueDegree_eq_one_of_sup_upper_eq_top F E μ hsup hμ` states that,
under the same hypotheses, the relative residue degree
`f = extensionResidueDegree F (E.asPadicField) (intermediateEmbedding F E)`
equals `1`. Its proof is the group-theoretic route from the task context.

1. Let `w₀ = localGeometricFrobenius F`, whose degree is `ofAdd 1`
   (`localGeometricFrobenius_degree`).
2. By the hypothesis, `localProjection F w₀` lies in
   `E.field.fixingSubgroup ⊔ G_F^μ`. Since `G_F^μ` is normal
   (`absoluteUpperRamificationGroup_normal`), `Subgroup.mem_sup_of_normal_right`
   writes it as `g * h` with `g ∈ E.field.fixingSubgroup` and `h ∈ G_F^μ`.
3. Since `μ ≥ 0`, `h ∈ G_F^0` (`absoluteUpperRamificationGroup_antitone`). This
   group is the absolute inertia of the canonical realization
   (`absoluteUpperCanonicalInertia`), which is the kernel of
   `localResidueDegree F` (`localResidueDegree_ker`). Therefore
   `localResidueDegree F g = localResidueDegree F (g * h)`. This equals the
   Frobenius image of the degree of `w₀`, because `w₀` is a pullback pair.
4. So `w₁ = (g, localDegree F w₀)` is an element of the Weil pullback of `F`. Its
   projection `g` fixes `E`, so `w₁` lies in
   `pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)`. Its integer
   degree is `1`.
5. `intermediateWeilEquiv_symm_degree` gives
   `localDegreeInt F w₁ = f * localDegreeInt EP w'` for the preimage `w'` of
   `w₁` in `W_E`. Hence `1 = f * k` in `ℤ` with `f ≥ 0`, so
   `Int.eq_one_of_mul_eq_one_right` gives `f = 1`.

## Main theorem

The published simp lemma `localDegree_intermediateWeilMap` states
`localDegree F (intermediateWeilMap F E w) = localDegree EP w ^ f`. Rewriting
with `f = 1` from the auxiliary lemma and `pow_one` closes the goal.

## Relation to the source

This is the compatibility with unramified twists in Lemma `lem:trunc` of the
operator route note `operator-numerical-llc-route-2026-11-16`, lines 876–889.
The route note assumes that `E/K` is totally ramified. Here the residue degree
`1` is derived from transitivity of `G_F^μ` with `μ ≥ 0`. The upper group lies
in inertia, so some element of the image of `W_E` has degree `1` over `F`. The
proof does not use ramification indices. The
[statement's documentation](TruncationQuotientStatement.md) explains how the
hypothesis is translated.
