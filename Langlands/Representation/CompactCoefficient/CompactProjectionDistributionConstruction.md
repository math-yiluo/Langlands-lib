# Constructing compact-representation Hecke projectors

Author: Worker 142.

This is an internal construction for Renard IV.1.5 (printed p.92 / PDF p.98),
using the published compact-isotypic splitting instead of the formal degree.
The left translation representation on test functions is smooth by common
compact open bi-invariance. Apply the intrinsic projector for the class of
`τ` to the normalized indicator of `K`. Integration against a fixed vector
is an intertwiner from the left regular representation to any smooth
representation, so cross-universe naturality computes the resulting Hecke
action. The intrinsic projector acts as the identity on `τ` and vanishes on
an inequivalent irreducible representation. This proves existence with the
prescribed actions; uniqueness and the compatibility laws are not asserted
in this module.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French edition of 9 July 2026, IV.1.5. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The implemented route is a derived proof from the Library's intrinsic
compact-isotypic splitting and its naturality, rather than Renard's
formal-degree formula.
