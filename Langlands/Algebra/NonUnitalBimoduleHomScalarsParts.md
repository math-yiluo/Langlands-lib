# Inherited coefficients on exact nondegenerate residual Hom parts

This module supplies the two exact-part constructions for the internal
sufficient-input adapter `NonUnitalBimoduleHomScalars`. It uses the original
`nondegeneratePart`, its original subtype additive group, and its inherited
`NonUnitalSubmodule` action. The coefficient ring, both nonunital rings, and
each original carrier have independent universes. No coefficient Module on an
original carrier is an input, and neither ambient Hom space is assumed
nondegenerate. The interfaces admit zero and subsingleton cases.

## Named coefficients and sufficient input

For the left orientation, the ambient carrier is exactly
`H = NonUnitalModuleHom R X Z`. Its coefficients are exactly
`NondegenerateModuleHomScalars.homModule k hR hRZ`, and its residual action is
exactly `NonUnitalBimoduleHomActions.sourceAction hX`. Every declaration
explicitly installs these two structures. The part is exactly
`nondegeneratePart hS H` for that original action.

`sourcePartModule` gives its named inherited coefficient Module, and
`sourcePartInclusion` gives the actual coefficient-linear subtype inclusion.
These constructions and coefficient closure need only target recovery and
pointwise commutation with precomposition. The compatible algebra action and
recovery comparison additionally use `SourceCompatible k hR hRX`, precisely
`IsScalarTower k Sᵐᵒᵖ X` relative to
`NondegenerateScalars.module k hR hRX`. This predicate comes from the ambient
module and contains no output compatibility assumption. No nondegeneracy for
the original right `S`-action on `X` is required.

For the right orientation, the ambient carrier is exactly
`H' = NonUnitalModuleHom Sᵐᵒᵖ Y Z`, with exactly the pointwise coefficients
`NondegenerateModuleHomScalars.homModule k hS.op hSZ` and original action
`NonUnitalBimoduleHomActions.rightSourceAction hY`. The part is exactly
`nondegeneratePart hR.op H'`. The names `rightSourcePartModule` and
`rightSourcePartInclusion` give the mirrored constructions directly, without
an opposite-action transport. `RightSourceCompatible k hS hSY` is precisely
`IsScalarTower k R Y` relative to
`NondegenerateScalars.module k hS.op hSY`. No left `R`-nondegeneracy of `Y` is
required.

The recovering ring has its specified coefficient Module and both
multiplication compatibility laws. For the Module comparison, both laws are
also required on the residual ring. Opposite rings use the coefficients
induced from the specified original-ring Module. There is no unit-action,
commutativity of either nonunital ring, nontriviality, finite-dimensionality,
or equal-universe hypothesis. Part closure and inclusion do not require the
extra source compatibility.

## Construction and implemented proofs

The reusable `CompatiblePart` namespace takes an arbitrary original
nonunital action and an ambient coefficient Module. Its `fixed_smul` lemma
uses scalar commutation to prove that the same idempotent fixing `v` also
fixes `c • v`. Its `smul_mem` lemma retains that exact witness.
`CompatiblePart.module` then defines coefficient scaling on the unchanged
subtype by `c • v = ⟨c • v.val, ...⟩`. The Module laws are inherited from the
ambient laws using subtype extensionality.

`smul_val_function` identifies the entire function obtained by scaling and
then including the part. `smul_subtype_toAddMonoidHom` gives the corresponding
equality of complete additive maps, expressed as composition with the
original subtype inclusion and the scalar multiple of the identity map.
`smul_val` is its pointwise form. The linear map `inclusion` has exactly the
original subtype additive map and exactly the function `Subtype.val`, as
proved by `inclusion_toAddMonoidHom` and `inclusion_function`.

The inherited original ring action remains in force throughout. The
compatibility lemmas `isScalarTower` and `smulCommClass` restrict the ambient
laws by subtype extensionality. `actionHom` packages those laws through
`NonUnitalModule.toLinearEndHom`. The whole action structure after forgetting
coefficients equals the original inherited subtype action, by
`ofLinearEndHom_actionHom`; `actionHom_toAddMonoidHom` and
`actionHom_function` identify its entire per-scalar additive map and function.

`recoveredModule_eq` installs the inherited coefficient Module and its derived
tower, then applies `NondegenerateScalars.module_eq_of_compatible` using
exactly `nondegeneratePart_isNondegenerate hA`. Its result is equality of
actual Module structures, rather than only equality of a selected scalar
formula. `recovered_smul_eq` rewrites that Module equality to compare both
coefficient actions on every actual part element.

The public Hom-specific declarations instantiate this helper with the
intrinsically derived ambient compatibility laws. In the left orientation,
`sourcePart_fixed_smul` and `sourcePart_smul_mem` retain a fixing idempotent,
`sourcePart_smul_val_function` and
`sourcePart_smul_subtype_toAddMonoidHom` give the complete inclusion identities,
and `sourcePart_smul_apply` gives `(c • f).val x = c • f.val x` using exactly
the recovered target coefficients. The inclusion has the full additive-map,
function, and evaluation identifications named
`sourcePartInclusion_toAddMonoidHom`, `sourcePartInclusion_function`, and
`sourcePartInclusion_apply`.

`sourcePartIsScalarTower` derives the part tower from the supplied source
compatibility through `sourceIsScalarTower`. `sourcePartSmulCommClass` derives
commutation from `sourceSmulCommClass`.
`sourcePartActionHom : S →ₙₐ[k] Module.End k (nondegeneratePart hS H)` is the
actual compatible algebra action. Its whole original-action equality is
`sourcePartActionHom_ofLinearEndHom`. The full additive map after inclusion
is the original ambient precomposition, as proved by
`sourcePartActionHom_subtype_toAddMonoidHom`. Its evaluation formula is
`(sourcePartActionHom ... s f).val x = f.val (op s • x)`, and the original
subtype action itself has that same formula. Finally,
`sourcePartRecoveredModule_eq` uses exactly
`nondegeneratePart_isNondegenerate (M := H) hS` and identifies recovered
coefficients with `sourcePartModule`; `sourcePart_recovered_smul_eq` exposes
the resulting elementwise equality.

The corresponding `rightSourcePart*` declarations provide all these results
on `H'` and its exact original part. At `op r`, the action evaluates to
`f.val (r • y)`, and the full additive map after inclusion is
`precomposeAddHom (hY.leftActionHom r)` composed with the original inclusion.
`rightSourcePartRecoveredModule_eq` uses exactly
`nondegeneratePart_isNondegenerate (M := H') hR.op`, comparing the recovered
Module with `rightSourcePartModule`. These are direct wrappers of the original
right source action, preserving the original actions, carriers, and groups.

## Provenance and remaining parent obligations

This is derived internal infrastructure, rather than a verbatim definition
from the source. It combines the published original residual Hom actions,
pointwise recovered Hom coefficients, compatible-action conversion, and
uniqueness of compatible recovered coefficients. The actual constructions
and short intrinsic proofs are grouped in this pair; complex specializations
and interface examples are supplied by the companion specialization module.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are I.1.1, printed pp.5–6 / PDF11–12 (original module
and commuting-action conventions); I.2.1, printed p.14 / PDF20 (recovered
coefficients); I.2.2–I.2.3, printed pp.15–18 / PDF21–24 (Hom and
nondegenerate-part use); and I.4.2, printed pp.23–24 / PDF29–30 (downstream
duality motivation). These passages and
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, were read. The 2026 edition governs.

The source works over complex coefficients. General commutative coefficient
rings and these named sufficient-input adapters are internal extensions.
The explicit compatibility with the named recovered source Module is part
of the result's scope: arbitrary commuting additive actions alone are not
used to identify separately recovered coefficient Modules. The full-source
I.4.2 coefficient convention remains an obligation of the parent, as do F/P
comparisons, duality equivalences, Hom-chain and categorical natural
isomorphisms, and dual-completion results. This pair claims none of them.
