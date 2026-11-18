# Torsion evaluations of the cubic direct image and the projective frame locus

This internal module defines the projective frame condition used to cover the
ordinary polarized full-level moduli functor by charts. All schemes lie in one
arbitrary universe `u`. Fix `P : Prerequisites.{u}`, a scheme `S`, natural
numbers `g d n`, and a datum `a : Datum P S g d n` with abelian structure map
`π = a.abelian.X.hom`, canonical cubic bundle `L³ = a.cubicBundle` and cubic
direct image `V = a.rigidificationModule = π_* L³`.

## Definitions

- `Datum.torsionPoint a r : S ⟶ a.abelian.X.left`, for a coefficient tuple
  `r : Fin (2*g) → ZMod n`, is the underlying morphism of the published torsion
  section `enumerateTuple a.level.sections r`. This section is the
  `ZMod n`-linear combination of the ordered level sections with coefficients
  `r`. `Datum.torsionPoint_hom` records that it is a section:
  `a.torsionPoint r ≫ π = 𝟙 S`.
- `Datum.torsionEvaluation a r : V ⟶ (a.torsionPoint r)^* L³` evaluates
  sections of `L³` at that torsion point. It is the composite of:
  - the identifications `V ≅ (𝟙 S)^* V ≅ (a.torsionPoint r ≫ π)^* V ≅
    (a.torsionPoint r)^* π^* V`, from Mathlib's `pullbackId`, `pullbackCongr`
    and `pullbackComp`;
  - the pullback along the torsion point of the published cubic evaluation
    counit `a.cubicEvaluationAdjoint : π^* π_* L³ ⟶ L³`.
- `Datum.frameEvaluation a ρ k`, for `ρ : Fin (m + 2) → Fin (2*g) → ZMod n` and
  `k : Fin (m + 2)`, is the morphism from `V` to the product of the line
  bundles `(a.torsionPoint (ρ j))^* L³` over all `j ≠ k`. Its components are the
  torsion evaluations.
- `Datum.frameLocus a ρ : S.Opens` is the supremum of all opens `W` of `S` such
  that, for every `k`, the pullback of `a.frameEvaluation ρ k` along the open
  inclusion `W.ι` is an isomorphism.

## Meaning

Suppose `V` is locally free of rank `m + 1`. This holds over locally noetherian
bases with `m + 1 = 6^g·d`, by the published `cubicDirectImage`. Then the frame
locus is the open set of base points where the `m + 2` torsion points
`P_{ρ_0}, …, P_{ρ_{m+1}}` map to a projective frame of the projectivized
fibre of `V`: any `m + 1` of the evaluation functionals form a basis of the
dual. Over the frame locus, the evaluations at `ρ_0, …, ρ_m` identify `V` with
a sum of line bundles, and the last point normalizes the coordinates. So the
cubic embedding of the abelian scheme becomes canonically a closed subscheme of
a fixed projective space. This is the frame normalization of a linear
rigidification in the sense of Mumford–Fogarty–Kirwan, *Geometric Invariant
Theory*, Definition 7.5 (printed p.130, PDF p.143 of the registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`).
The frame is formed by the images of torsion points, the covariant of GIT
Corollary 7.8.

This module states no theorem about the frame locus beyond the section
identity. Base-change compatibility, invariance under polarized isomorphisms
and covering for large `n` are separate results.

## Provenance

This is an internal construction from published Library objects
(`enumerateTuple`, `Datum.cubicEvaluationAdjoint`,
`Datum.rigidificationModule`) and Mathlib's module pullback isomorphisms. The
frame idea follows GIT §7.2–§7.3 as cited above.
