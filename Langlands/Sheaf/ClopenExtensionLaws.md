# Naturality and nested images of clopen zero extension

Downstream laws: Worker 865, using Worker 6's core construction.

For an actual Mathlib sheaf of abelian groups, with independent space and group
universes, this module proves that its clopen zero extension commutes with actual
sheaf morphisms. Both composites have the same restriction to the clopen and
vanish on its complement, so categorical gluing uniqueness proves equality.

Restriction through an intermediate open is direct restriction, by presheaf
functoriality. Consequently zero extension vanishes on every open contained in
the complementary open. If closed opens satisfy `U ≤ V`, the complement of `V`
is contained in the complement of `U`. The extension from `U` therefore vanishes
there. Uniqueness for the disjoint cover by `V` and its complement shows that
restricting this extension to `V` and extending again gives the original
extension.

`image` is the actual `AddSubgroup` range of the additive zero-extension map.
The nested compatibility supplies a preimage under extension from `V` for every
section in the range of extension from `U`, and proves `image_mono`.

These are internal all-open laws motivated by David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, II.2.4, printed p.38
/ PDF p.44, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original proposition concerns sheaves on a compact-open basis and compact
support. The present declarations concern all opens and closed opens only.
Basis comparisons, stalk support and compact-support exhaustion are separate
obligations.
