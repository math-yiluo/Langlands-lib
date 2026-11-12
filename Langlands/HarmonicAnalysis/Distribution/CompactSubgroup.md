# Normalized Haar distributions on compact subgroups

This definition unit constructs Renard's `e_Γ` for every compact subgroup,
including compact subgroups that are not open. It reuses the published
`Distribution G` and `compactlySupported` submodule. The group is Hausdorff,
locally compact and totally disconnected, with its supplied topology.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locator: II.3.11, first paragraph and displayed definition, printed p.51 /
PDF p.57. The same paragraph evaluates `e_Γ` on locally constant functions;
comparison with the published extended pairing remains a statement obligation.

`Distribution.compactSubgroupDistribution K hK` is the concrete complex-linear
functional `f ↦ ∫ k:K, f(k) dμ_K`, using the actual subgroup with its induced
topology and Borel measurable space. Compactness provides a `CompactSpace K`
instance. Mathlib's `Measure.haarMeasure ⊤` is normalized on the whole compact
group; `Measure.haarMeasure_self` gives mass one. Every integrand is continuous
on that compact group, so the integral is integrable, and integral linearity
supplies the linear-map fields. The measure is constructed, not supplied as
arbitrary functional data.

The implemented support proof observes that a test vanishing on `K` has zero
integral. The existing `support_subset_of_mem_supportedOn` therefore bounds the
topological distribution support by the compact closed set `K`.
`compactSubgroupHaar K hK` is this same distribution with that compactness proof.
The coercion theorem is definitional, and `compactSubgroupHaar_apply` records
the exact ambient-test integral. This construction supplies the compact support
needed for the definition; it does not assert the later uniqueness, translation
invariance, extended mass-one pairing, product, conjugation or Hecke membership
formulas. Those II.3.11–II.3.12 assertions require their own statements and proofs.

The existing `Hecke.HeckeAlgebra.normalizedIndicator` is a function realization
for compact **open** subgroups relative to an ambient Haar measure. It does not
replace this distribution on arbitrary compact subgroups; its exact density
comparison is a subsequent obligation. No new distribution carrier or second
Hecke algebra is introduced here.
