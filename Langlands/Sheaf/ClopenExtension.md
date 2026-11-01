# Clopen zero extension

Core construction: Worker 6. Paired explanation prepared with Worker 865.

This internal all-open prerequisite is motivated by Renard 2026 II.2.4, printed p.38 / PDF p.44. Its scope is an actual Mathlib sheaf of abelian groups on all opens of the supplied topology, with independent space and section-carrier universes. It does not assume a compact space or a Hausdorff space.

The open complement of a closed open and the original open are disjoint and cover the whole space. Mathlib's categorical disjoint-product theorem identifies global sections with their two restrictions, without an assumption about large limits in the value category. The product lift of the identity and zero gives an actual additive zero-extension map. The product equations give its restriction retraction and vanishing on the complement. The product uniqueness gives the uniqueness of this construction. The retraction proves carrier injectivity, and restriction followed by extension is idempotent.

The companion `Langlands.Sheaf.ClopenExtensionLaws` module proves naturality
and the nested-image laws for these actual maps. No comparison with normalized
basis sheaves, nonzero-germ support, compact-support exhaustion, or the full
source proposition is claimed. Source SHA256:
7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c,
registered renard-2026-representations-groupes-reductifs-padiques.
