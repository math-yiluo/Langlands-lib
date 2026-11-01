# Tensor-dual preservation and actual-part restrictions

Workers 321 and 702. This pair is derived internal infrastructure for David
Renard, *Représentations des groupes réductifs p-adiques*, French version of
9 July 2026, I.4.1–I.4.2, printed pp.22–24 / PDF28–30, especially the
tensor-Hom argument on PDF30. The original additive module and recovered
coefficient conventions are I.1.1, printed pp.5–6 / PDF11–12, and I.2.1–I.2.2,
printed pp.14–16 / PDF20–22. The registered governing source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, corrects nearby adjunction and corner arguments; the 2026 text governs.

## Exact original objects and coefficients

This module imports the actual ambient evaluation and balanced quotient-lift
maps from `NonUnitalTensorDualMaps`. S, R, X and M retain independent universes.
The inputs are the original additive groups, specified nonunital actions,
idempotented complex algebras S and R, commuting left S/right R actions on X,
nondegeneracy of both those actions on X, and nondegeneracy of the left R-action
on M. No carrier coefficient Module or comparison map is an input.

Write T for the original additive `NonUnitalModuleTensor.Tensor R X M`, HS
for exactly `NonUnitalBimoduleTensor.leftModule hX M`, and hT for exactly
`NondegenerateTensorFunctor.isNondegenerate hS hX hSX M`. F and DT are the
published `FullDual hS hT` and `Dual hS hT` using HS. DM is exactly
`NonUnitalModuleDual.Dual hR hM`, with its published `dualAction`. H is the
original `NonUnitalModuleHom Rᵐᵒᵖ X DM`. The local aliases select the following
structures explicitly; they introduce no new action or replacement carrier.

| Alias | Selected published structure |
| --- | --- |
| `fullAction` | `NonUnitalModuleDual.fullAction hS hT` on F |
| `homAction` | `NonUnitalBimoduleHomActions.rightSourceAction hX` on H |
| `HomPart` | Exactly `nondegeneratePart hS.op H` for `homAction` |
| `partAction` | The inherited original right S-action on that exact subtype HP |
| `dualAction` | `NonUnitalModuleDual.dualAction hS hT` on DT |
| `fullCoefficients` | The usual pointwise complex Module on F |
| `homCoefficients` | `NondegenerateModuleHomScalars.homModule ℂ hR.op (NonUnitalModuleDual.isNondegenerate hR hM)` |
| `partCoefficients` | `NonUnitalBimoduleHomScalars.rightSourcePartModule ℂ hS hR hX (NonUnitalModuleDual.isNondegenerate hR hM)` |
| `dualCoefficients` | `NonUnitalModuleDual.dualModule hS hT` |

The additional input hc is precisely
`NonUnitalBimoduleTensorScalars.InputCompatible ℂ (S := S) hR hRX`.
It asserts the scalar tower for the original left S-action on X relative to
exactly `NondegenerateScalars.module ℂ hR.op hRX`. The imported
`inputCompatible_iff_rightSourceCompatible` identifies the Hom adapter's
formulation on the same original data. This is an explicit sufficient
hypothesis; commutation of the original additive actions alone does not imply
it. See the published
[coefficient-convention note](../../notes/renard/duality-coefficient-conventions.md).

Two named lemmas retain the proved coefficient comparisons.
`targetRecoveredCoefficients_eq` is the published equality between coefficients
recovered from DM's original right R-action and its named `dualModule`.
`partRecoveredCoefficients_eq` specializes
`rightSourcePartRecoveredModule_eq` to DM and the exact intrinsic
`nondegeneratePart_isNondegenerate` proof for HP. The latter equality uses
hRX and hc. Neither equality is an assumed certificate.

## Preservation and the implemented restriction

Write C and U for the imported actual `curry` and `uncurry`. Their included
formulas are `C ell x m = ell (tmul R X M x m)` and
`U h (tmul R X M x m) = (h x).val m`. In the first formula inclusion of
`C ell x` in the full dual of M is understood. The imported construction
proves inner-dual landing using an actual original R-idempotent fixing x and
balancing. Its reverse map is the actual original balanced additive quotient
lift, with coefficient linearity transferred by the proved tensor Module
equality.

`full_ext` proves equality of full functionals from equality on all original
pure tensors, by `NonUnitalModuleTensor.hom_ext` and injectivity of the
underlying additive-map projection. `curryAdd` proves additivity by extensionality
on x and m; `uncurryAddMap` uses `full_ext`. These bundles keep the actual C and U
as their functions.

`curry_action` and `uncurry_action` prove original right S-equivariance for
exactly `fullAction` and `homAction`. Evaluation reduces both claims to the
same value on a pure tensor. They give the actual ambient original-action
maps `curryHom` and `uncurryHom`.

`curryLinear` and `uncurryLinear` refine the same additive maps using exactly
`fullCoefficients` and `homCoefficients`. Their scalar proofs reduce to
pointwise evaluation and `NonUnitalModuleDual.canonical_smul_apply` on DM.
That dependency uses the proved equality between recovered and named DM
coefficients. `curryLinear_toAddMonoidHom` and
`uncurryLinear_toAddMonoidHom` identify the entire additive maps by reflexivity.

For each actual idempotent e of S, `curry_fixed_iff` proves that `op e` fixes
ell if and only if it fixes C ell. Forward preservation follows from
`curry_action`; the reverse direction evaluates the fixing equality at every
x and m and then uses `full_ext`. It uses no inverse identity.
`uncurry_fixed` proves that the same specified e fixing h fixes U h, using
`uncurry_action`.

`curryPart : DT → HP` and `uncurryPart : HP → DT` use the precise fixing
idempotent supplied by the original input subtype's membership proof. Original
action preservation transports that same witness to the output; the proof
does not assume nondegeneracy of the whole ambient dual or Hom. The resulting
maps are actual restrictions of C and U.
`curryPart_val_function` and `uncurryPart_val_function` give the entire included
functions, and `curryPart_apply` and `uncurryPart_tmul` expose their literal
values on the original pure tensors.

`curryPartHom` and `uncurryPartHom` bundle these functions as original
`NonUnitalModuleHom Sᵐᵒᵖ`, with precisely `dualAction` and `partAction`.
The additive and original-action laws descend from the ambient laws by subtype
extensionality. `dualInclusion` is exactly the published original dual
inclusion and `partInclusion` is exactly the original Hom-part subtype map.
`curryPartHom_inclusion` and `uncurryPartHom_inclusion` state equality of the
complete inclusion composites as original-action maps, by reflexivity.

Finally, `curryPartLinear` and `uncurryPartLinear` use the named
`dualCoefficients` and `partCoefficients`, and the same additive maps as the
restricted original-action bundles. Their scalar proofs are the ambient
linear-map scalar laws followed by subtype extensionality. The two
`PartLinear_toAddMonoidHom` lemmas identify the entire underlying additive
maps. `curryPart_smul` and `uncurryPart_smul` state the scalar laws for these
exact named Modules. Their `_val` versions retain the whole ambient values
after the original inclusions. `curryPart_smul_apply` and
`uncurryPart_smul_tmul` give the further scalar evaluation formulas on every
original pure tensor; the reverse formula again uses
`canonical_smul_apply` on DM.

## Scope

This pair supplies preservation, same-idempotent restriction, original-action
inclusion identities and coefficient-linear refinements of the actual ambient
maps. Its source-derived proof route is the evaluation and nondegenerate-image
argument of I.4.2 with an explicit sufficient coefficient input. The complete
interface and concrete-example checks are a separate focused pair in this
task. Inverse identities, a comparison equivalence, categorical naturality,
actual F/P specialization and the full-source coefficient-convention
obligation remain separate work; none is concluded by this pair.
