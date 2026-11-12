# Stalks of a complex vector sheaf as quotients of compact sections

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, the Remarque on printed p.42 /
PDF p.48, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Remark describes the stalk at `x` of `F ∈ C^∞_X-Mod(X)` as
`F_x = F_c(X) / ⟨f · φ, φ ∈ F_c(X), f ∈ D(X), f(x) = 0⟩`.
This file constructs the objects in that description and the canonical map.
It does not prove that the map is bijective. That is a separate statement
for a later proof task.

## Objects

`X : Type` carries a topology, and `F : VectorSheafScalars.VectorSheaf X` is
a Mathlib sheaf of complex vector spaces. Its compact sections are the
published `CompactSupport.submodule F.presheaf`. The test action is the
`CompactSectionTestModule.testModule` instance of the pointwise test algebra
`PointwiseTestAlgebra.Carrier X` (Renard's `D(X)`). The universe is `Type`
for the same reason as in `CompactSectionTestModule`.

- `vanishingGenerators F x` is the set of `f • s` with `f : D(X)`, `s` a
  compact section, and `f x = 0`.
- `vanishingSpan F x` is its complex span, Renard's
  `⟨f · φ, f(x) = 0⟩`, as a `Submodule ℂ` of the original compact sections.
  `smul_mem_vanishingSpan` records that the generators lie in it.

## The canonical map

The actual stalk is Mathlib's colimit stalk `F.presheaf.stalk x`. The germ map
is the published `CompactGerms.germ F x`, the global germ restricted to compact
sections. `germ_testSmul` proves `(f • s)_x = f(x) • s_x`. Hence
`vanishingSpan_le_ker` proves that the germ map kills the span.
`stalkQuotientMap F x` is the induced complex-linear map
`F_c(X) / ⟨f · φ, f(x) = 0⟩ → F_x` (Mathlib's `Submodule.liftQ`), and
`stalkQuotientMap_mk` gives its value on classes.

`stalkQuotientMap_surjective` assumes
`hX : Langlands.Topology.IsLocallyProfinite X`. It follows from the published
surjectivity `CompactGerms.germ_surjective`, which extends a germ by zero
from a compact open neighborhood. The Remark derives this from the exact
sequence in the preceding Proposition. Injectivity, identifying the kernel of
the germ map with the span, is the substantive part of the Remark. It is not
proved here.

## Naturality

For a morphism `φ : F ⟶ G`, `vanishingSpan_le_comap` proves that the published
`CompactSupport.map φ.hom` sends the span of `F` into that of `G`. The proof
uses the test-linearity `compactSectionMap` from `CompactSectionTestModule`.
`quotientMap x φ` is the induced map of quotients (Mathlib's
`Submodule.mapQ`). `stalkQuotientMap_naturality` proves that Mathlib's stalk
map of `φ` composed with `stalkQuotientMap F x` equals
`stalkQuotientMap G x` composed with `quotientMap x φ`.
It reduces to the published `CompactGerms.germ_naturality` on classes.

Worker 184 implements this unit for Task 5338.
