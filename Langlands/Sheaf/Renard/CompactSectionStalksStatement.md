# Statement: stalks are quotients of compact sections

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, the Remarque on printed p.42 /
PDF p.48, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Remark states, for `F ∈ C^∞_X-Mod(X)` and `x ∈ X`,
`F_x = F_c(X) / ⟨f · φ, φ ∈ F_c(X), f ∈ D(X), f(x) = 0⟩`.

`StalkQuotientComparison` is the closed proposition: for every `X : Type`
with a topology satisfying `Langlands.Topology.IsLocallyProfinite X`
(Hausdorff with a basis of compact open neighborhoods, Renard's t.d.
spaces), every complex vector sheaf `F : VectorSheafScalars.VectorSheaf X`
and every point `x`, the canonical map
`CompactSectionStalks.stalkQuotientMap F x` is bijective.

That map is the one induced on the quotient of the published compact
sections `CompactSupport.submodule F.presheaf` by
`CompactSectionStalks.vanishingSpan F x` (the complex span of the `f • s`
with `f(x) = 0`, for the test action of `CompactSectionTestModule`) by the
published germ map `CompactGerms.germ F x` into Mathlib's stalk
`F.presheaf.stalk x`. The identification in the Remark is therefore asserted
through this canonical map and not through an arbitrary isomorphism.

Surjectivity is already proved as
`CompactSectionStalks.stalkQuotientMap_surjective`. The remaining proof
obligation is injectivity. Equivalently, a compact section with zero germ
at `x` lies in the span. The source's argument takes a compact open
containing the support of the section and avoiding `x`; its characteristic
function vanishes at `x` and fixes the section.

The universe is `Type`, as in `CompactSupport` and `CompactGerms`, which tie
the space, the coefficient field and the section carriers to one universe.
This file states the proposition only; it proves nothing.

Worker 184 implements this statement for Task 5338.
