# Proof of finite-type adelic-level model comparison

Author: Worker 208.

`adelicFiniteTypeLevelModelComparison` proves exactly
`AdelicFiniteTypeLevelModelComparisonStatement` in its arbitrary common
universe, with the original actual arithmetic level maps and all the
statement's hypotheses preserved.

For each arithmetic base, `adelicSIntegersNoetherian` gives
`IsNoetherianRing` for the actual S-integer ring, without changing that
ring's carrier or operations. Mathlib makes its spectrum locally
Noetherian. Applying
`LocallyOfFiniteType.isLocallyNoetherian` to the original structure
morphism makes the original model locally Noetherian. Mathlib's
`IsLocallyNoetherian.quasiSeparatedSpace` then supplies
quasi-separatedness, and the actual level-model injectivity theorem
applies. This argument only needs local finite type.

For the separate finite-type conclusion, the quasi-compact structure
morphism has quasi-compact source because its actual affine target is
quasi-compact. The proof uses
`QuasiCompact.compactSpace_of_compactSpace` for this step. The general
actual level-model surjectivity theorem now applies, since each
original completed field or completed valuation ring is local.
Combining it with the injectivity just proved gives bijectivity.

The implemented proof follows the reduction in Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011), printed
pp.6–8, Theorem 3.6, (3.6.1)–(3.6.2), through the separately proved
arithmetic Noetherianity and actual local-product comparison.
Registered contextual source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arithmetic proof also justifies arbitrary constants and empty
`S` in the function-field clause.

This proves set comparisons. Nonaffine point topologies, transition
maps, model descent, the adelic colimit, model independence and the
global-function-field presentation comparison remain as stated in
the target's Markdown.
