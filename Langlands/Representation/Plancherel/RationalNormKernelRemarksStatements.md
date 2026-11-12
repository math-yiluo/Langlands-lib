# Remaining assertions of Renard V.2.3, V.2.5 and V.2.6 on the norm kernel `⁰G`: statements

Module `Langlands.Representation.Plancherel.RationalNormKernelRemarksStatements`.
Namespace `Langlands.Plancherel`. Universe parameter `u`.
The module contains three **statements**, the `Prop`-valued definitions
`RationalNormKernelUnimodularStatement`, `RationalNormKernelRestrictionStatement` and
`RationalNormKernelCompactCenterStatement`. It proves nothing.

Worker 1222 wrote this statement unit under the whole-book task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The Chapter V item ledger found that every other
assertion of these three paragraphs is published. These are the assertions it found
unstated. The V.2.6 Lemma assertion `⁰A_G = ⁰G ∩ A_G` is not restated here: it is the
published `Langlands.Plancherel.RenardCartan.SplitComponentKernelStatement` (module
`RenardLatticeComparisonStatement`).

## Source and provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1222 read V.2.3–V.2.6, printed pp.105–108 / PDF pp.111–114.

- V.2.3, Proposition (printed p.106 / PDF p.112): « Le groupe `⁰G` est un sous-groupe
  ouvert, fermé et distingué unimodulaire de `G`. […] ». The proof ends: « Comme `⁰G`
  contient des sous-groupes ouverts compacts, il doit être ouvert dans `G`. Il est donc
  unimodulaire car `G` l'est. »
- V.2.5, last paragraph (printed p.107 / PDF p.113): « Si `A₁` et `A₂` sont deux tores
  déployés définis sur `F`, avec `A₁ ⊂ A₂`, alors `Λ(A₁) ⊂ Λ(A₂)`. En effet, d'après ce qui
  précède, on voit facilement que `⁰A₁ = A₁ ∩ ⁰A₂`. »
- V.2.6, Lemma (printed p.108 / PDF p.114): « On a `⁰A_G = ⁰G ∩ A_G`. […] »
- V.2.6, Proposition (printed p.108 / PDF p.114): « Le quotient `G/⁰G A_G` est fini, et
  `⁰G ∩ Z(G)` est compact. Si `Z(G)` est compact, alors `⁰G = G`. »

Here `⁰G` is the intersection of the kernels of `|χ|_F` over the rational characters
`χ` of `G` (V.2.3). `A_G` is the split component of `G`, a maximal split torus in its centre
(V.2.1).

## Published objects used

- `rationalCommonNormKernel G` (module `RationalCharacterValuation`): Renard's `⁰G`, the
  common kernel of the normalized norms `g ↦ |χ(g)|_F` of all rational characters `χ`. Its
  Markdown records this correspondence.
- `GroupScheme.rationalPoints G` with `rationalPointTopology F G.X`: the actual group `G(F)`
  with its canonical topology. `GroupScheme.rationalPoints.map f` is the map on points.
- `isOpen_rationalCommonNormKernel G` (module `RationalNormKernelTopology`, proved): `⁰G` is
  open.
- `IsSplitTorus`, `IsSplitSubtorus` (split torus and closed immersion).
- Mathlib's `MeasureTheory.Measure.modularCharacter`.

## The statements

**`RationalNormKernelUnimodularStatement` (V.2.3).** Let `G` be connected reductive over a
nonarchimedean local field `F`, and give `G(F)` the canonical topology. Assume `G(F)` is
locally compact, Hausdorff and a nonarchimedean group. Then the modular character of `⁰G`
is identically 1. These three properties appear as instance binders, as in the published
`RationalNormKernelUniformSupportStatement` and `RationalReductiveUnimodularityStatement`.
`⁰G` carries the subspace topology. It is locally compact because it is open; the statement
installs that instance from `isOpen_rationalCommonNormKernel` and
`IsOpen.locallyCompactSpace`.

**`RationalNormKernelRestrictionStatement` (V.2.5).** For split tori `A₁`, `A₂` over `F` and
a split subtorus `f : A₁ ⟶ A₂`, the inverse image of `⁰A₂` under `f : A₁(F) → A₂(F)` is `⁰A₁`.
Since `f` is a closed immersion, its map on points is injective, and this is Renard's
equality of subgroups `⁰A₁ = A₁ ∩ ⁰A₂`. The analogous equality `⁰A_G = A_G ∩ ⁰G` for the
split component (V.2.6, Lemma) is the published `SplitComponentKernelStatement`, in the same
inverse-image form.

**`RationalNormKernelCompactCenterStatement` (V.2.6, Proposition).** For connected
reductive `G`, if the centre of `G(F)` is compact in the canonical topology, then
`⁰G = G(F)`.

## Formalization choices

- **Centre.** The statement uses the abstract centre `Subgroup.center (rationalPoints G)` of
  `G(F)`. The proved `rationalCenterComparison` identifies it with the points of the scheme
  centre, Renard's `Z(G)`.
- **Inclusion of tori.** Renard's `A₁ ⊂ A₂` is a split subtorus, the published
  `IsSplitSubtorus f`: `A₁` is a split torus and `f` is a closed immersion.
- **Field.** As in the published `rationalCommonNormKernel` interface, `F` is any
  nonarchimedean local field, of any characteristic.

## Related Library content

The other assertions of the V.2.3 Proposition are proved: `isOpen_rationalCommonNormKernel`,
`isClosed_rationalCommonNormKernel`, the normality instance `rationalCommonNormKernel_normal`,
`compactSubgroup_le_rationalCommonNormKernel` and `derivedPoints_le_rationalCommonNormKernel`.
Unimodularity of `G(F)` (V.5.4) is the proved `rationalReductiveUnimodularity`. For V.2.6,
the equality `⁰A_G = ⁰G ∩ A_G` is the published, not yet proved
`RenardCartan.SplitComponentKernelStatement`, and the finite index of `Λ(A_G)` in `Λ(G)` is
the proved `splitComponentLattice`. The finiteness
of `G/⁰G A_G` follows from it by `finite_rationalCentralQuotient`, and compactness of
`⁰G ∩ Z(G)` is `isCompact_rationalCommonNormKernel_inf_center`.

## Why the statements are true

- Unimodularity: `⁰G` is open in the unimodular group `G(F)`, so the restriction of a Haar
  measure of `G(F)` is a left and right Haar measure on `⁰G`.
- Restriction: one inclusion holds because rational characters of `A₂` restrict to
  rational characters of `A₁` (published `rationalCommonNormKernel_le_comap`). For the
  other, the restriction `X*(A₂) → X*(A₁)` along a closed subtorus of a split torus is
  surjective, so every `|χ(t)|_F` with `χ ∈ X*(A₁)` is some `|χ'(f t)|_F`. Renard's argument
  for `A_G ⊆ G` uses instead that the restriction has finite-index image (`|χ(t)|_F^m = 1`
  forces `|χ(t)|_F = 1`).
- Compact centre: `A_G(F)` is a closed subgroup of the compact centre, so it is compact.
  A split torus with compact group of points is trivial. Then `G/⁰G` is finite (V.2.6).
  It embeds in the torsion-free group `Λ(G)`, so it is trivial. Renard argues in the same
  way with powers of `g`.

## Remaining obligations

The proofs are separate obligations.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Plancherel.RationalNormKernelTopology` | `rationalCommonNormKernel`, `isOpen_rationalCommonNormKernel`, `rationalPointTopology`, `IsSplitSubtorus` (through its imports) |
| `Mathlib.MeasureTheory.Group.ModularCharacter` | `modularCharacter` |
