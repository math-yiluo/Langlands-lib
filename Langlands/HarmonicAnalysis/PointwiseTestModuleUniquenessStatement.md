# Uniqueness of smooth multipliers extending an original test action

This states the uniqueness assertion in David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026, II.2.5 lemma,
printed p.39 / PDF p.45. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The surrounding construction and theorem occupy printed pp.38–40 /
PDF pp.44–46. Those three original pages were read for this statement.

Renard starts from a nondegenerate module for the actual pointwise test
algebra `D(X)` and asserts a unique extension to the locally constant
smooth-function algebra. Nondegeneracy for the latter is relative to the
compact-open characteristic idempotents, as the 2026 text explicitly says.
The published [PointwiseTestModule](PointwiseTestModule.md) constructs that
extension on the unchanged original additive carrier, proves the source
formula and relative nondegeneracy, and preserves original intertwiners.
This new unit states its remaining uniqueness assertion.

## Exact target

The proposition is
`Langlands.HarmonicAnalysis.PointwiseTestModule.SmoothExtensionUniqueStatement X`.
For every independently sized additive group `M`, every specified original
`μM : NonUnitalModule (PointwiseTestAlgebra.Carrier X) M`, its actual
nondegeneracy witness `hM`, and every
`σM : Module (LocallyConstant X ℂ) M`, it asserts:

If every included test acts under `σM` exactly as the specified original test
acts under `μM`, then `σM = PointwiseTestModule.module hM`.
The premise explicitly selects `σM` locally and the original scalar operation
`μM.toDistribSMul.toSMul.smul`. The conclusion is equality of the actual module
structures on that same additive group. No preselected complex action,
change of carrier or replacement smooth-function algebra is used.

Only the natural extension-agreement premise is supplied for `σM`.
Relative nondegeneracy, scalar-tower compatibility, commutation and a
fixing-characteristic family are not additional assumptions. The published
original characteristic fixers and extension agreement already give relative
nondegeneracy for any such extension. The target itself concludes module
equality; it does not package a categorical equivalence.

The space and module universes are independent. The source specialization is
Renard's Hausdorff space with a compact-open neighborhood basis, whose
convention was read at II.1.1, printed p.30 / PDF p.36. Allowing any supplied
topology is the same derived generalization used by the published
compact-clopen construction. No separation, compactness, countability,
dimension or nonemptiness hypothesis is imposed. Empty spaces and zero
modules remain included.

## Proof and categorical boundary

This file exports a Prop-valued definition and no proof of it.
A prospective proof can derive scalar-tower compatibility from the actual
pointwise inclusion, the extension-agreement premise and the module
multiplication law, then use the published
`NondegenerateScalars.module_eq_of_compatible`. Equivalently, the original
characteristic fixer and the extension's module law force the source
formula. These are proof routes, not a proof publication.

Restriction/extension categorical equivalence, module-sheaf categories,
their natural inverse comparisons and the full sheaf/module theorem retain
their separate obligations.
