# Checks for compatible-input tensor-dual evaluation

Worker 321. This is a derived internal interface and example companion to
`NonUnitalTensorDualMaps` and `NonUnitalTensorDualMapsParts`. The governing
mathematical context is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, I.1.1, printed pp.5–6 / PDF11–12;
I.2.1–I.2.2, printed pp.14–16 / PDF20–22; and I.4.1–I.4.2, printed pp.22–24 /
PDF28–30, especially the tensor-Hom argument on PDF30. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, contains nearby adjunction and corner corrections; the 2026 text governs.
The universe, competing-instance and concrete numerical checks below are
internal consequences and regression checks, rather than separate assertions
quoted from that literature.

## Interfaces and selected original data

The four universes of S, R, X and M are independent. `CurryInterface` and
`UncurryInterface` spell out the complete unapplied ambient function types.
They use the original additive balanced tensor, its specified residual left
S-action, the full dual for the precisely specified tensor nondegeneracy
proof, and the original right-R Hom into the actual nondegenerate dual of M.
`PartHomInterface` spells out both restricted original right-S Hom types.
`PartLinearInterface` spells out both restricted complex-linear types using
the named `dualModule` and `rightSourcePartModule`. Each of these six interfaces
is checked at arbitrary independent universes and at the closed assignments
`(uS,uR,uX,uM) = (0,1,2,3)` and `(3,2,1,0)`.

None of these interfaces takes a carrier coefficient Module as an input.
The extra scalar compatibility is exactly
`NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX`.
It concerns coefficients on X recovered from its original right-R action.
The imported construction proves its identification with the Hom adapter's
`RightSourceCompatible` on the same data. Commuting original additive actions
alone do not supply this tower; the remaining convention issue is described in
the [coefficient-convention note](../../notes/renard/duality-coefficient-conventions.md).

`CompetingStructures` places additional coefficient Modules and original-action
instances on the factor, tensor, dual, Hom and part carriers in the local
instance context. Its checks explicitly reselect these published structures:

| Name | Selected structure |
| --- | --- |
| MX | `NondegenerateScalars.module ℂ hR.op hRX` on X |
| MM | `NondegenerateScalars.module ℂ hR hM` on M |
| MT | `NondegenerateTensorScalars.module ℂ R X M hR hM` on the original tensor |
| HS | `NonUnitalBimoduleTensor.leftModule hX M` |
| DM action and coefficients | The published `dualAction hR hM` and `dualModule hR hM` |
| F and DT action and coefficients | The full-dual and actual-dual structures for HS and its exact intrinsic nondegeneracy proof |
| H action and coefficients | `rightSourceAction hX` and `homModule ℂ hR.op (NonUnitalModuleDual.isNondegenerate hR hM)` |
| HP action and coefficients | The inherited original part action and `rightSourcePartModule ℂ hS hR hX (NonUnitalModuleDual.isNondegenerate hR hM)` |

The examples check instance selection, both factor scalar formulas on original
pure tensors, the tensor/DM/HP recovered-coefficient comparisons, both ambient
original right-S action laws, the restricted scalar evaluation formulas after
the original inclusions, and equality of the entire additive maps of the
restricted linear and original-action bundles. The coefficient comparisons
are applications of proved dependencies, not assumed equality certificates.

`CompetingOriginalActions` additionally names the original S-action on X,
right-R action on X and R-action on M before adding other such actions.
It then explicitly reselects the original actions in both the expected types
and proofs. The ambient formulas and restricted original right-S formulas
still concern the original balanced tensor and exact original inclusions.
Only these two deliberately overlapping-action examples locally disable the
overlapping-instances linter.

## Boundary checks and the nonzero regular example

`Boundary` checks that both ambient and both restricted constructions send zero
to zero. If either original factor X or M is subsingleton, it proves that both
ambient outputs are zero for arbitrary ambient inputs. The proofs show that
the input functional vanishes on every original pure tensor, use tensor
generator extensionality, and show that the input Hom vanishes by ordinary
map extensionality. No ambient full-dual or Hom nondegeneracy is assumed.

`RegularComplex` uses S = R = X = M = ℂ with the published original regular
left and right actions and their regular-action nondegeneracy lemmas.
The recovered left and right coefficient formulas are derived using
`NondegenerateScalars.scalarMul_eq` and the actual fixing idempotent 1:
they are respectively `c * m` and `x * c`. The required input tower is then
proved from the latter formula and the commutative ring laws.

`complexFunctional x` is the literal full-dual functional `m ↦ x * m`,
linear for the recovered left coefficients on M. `complexDual x` places it
in the actual dual using the original idempotent 1.
`complexHom` packages these functionals as an original right-R intertwiner,
using associativity of multiplication. The public definition
`regularComplexTensorFunctional` is the actual ambient `uncurry` of this Hom.
Thus it is the original balanced quotient lift constructed by the imported
module, rather than a functional obtained by identifying the tensor with ℂ.

`complexHomPart` belongs to the exact original residual Hom part because the
original idempotent 1 fixes `complexHom`. `complexTensorDual` is its actual
`uncurryPart`; its entire included functional equals
`regularComplexTensorFunctional` by reflexivity. Both ambient directions
and both restricted directions have the literal value `x * m` on the
original pure tensor `tmul ℂ ℂ ℂ x m`.

The examples evaluate at x = 2 and m = 3 to obtain 6. Applying the constructed
functional to a hypothetical vanishing pure tensor proves
`tmul ℂ ℂ ℂ (2 : ℂ) 3 ≠ 0`. Evaluation at the same inputs proves that the full
functional, its actual tensor-dual element, the constructed Hom part and the
actual restricted curry output are nonzero. These are concrete checks of the
actual maps and original carriers.

The use of 1 is confined to this regular complex example. The general
interfaces and checks impose no unit-action law on carriers, dimension,
admissibility or nondegeneracy of the ambient Hom. The imported construction
uses actual original fixing idempotents for inner-dual landing and for the
two restrictions, and an intrinsic balanced additive quotient lift for
uncurry, with coefficient linearity transferred by the proved tensor Module
comparison. This companion proves no inverse identities, comparison
equivalence, categorical naturality or actual F/P specialization. It makes
no unrestricted I.4.2 or full-source coefficient-convention claim.
