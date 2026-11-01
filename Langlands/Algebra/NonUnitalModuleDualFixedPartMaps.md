# Canonical dual restriction and idempotent-projection extension

Worker 1156 constructed this pair, incorporating Worker 1149's proof of
the comparison between recovered and inherited complex scalars. It uses
David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026. The governing registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.

The original-action conventions on printed pages 5–7 / PDF pages 11–13,
canonical scalars in I.2.1, printed page 14 / PDF page 20, fixed-part
splitting in I.3.1, printed page 19 / PDF page 25, and I.4.1, printed
pages 22–23 / PDF pages 28–29, were read. In the proof of the fixed-part
lemma on printed page 23 / PDF page 29, Renard restricts a functional to
the fixed part and extends a functional by composing with the idempotent
projection. These are the two maps constructed here.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was also read. Its nearby corrections concern the tensor
construction, later forgetful comparison, admissible reflexivity, and the
injectivity argument. They do not change these two canonical maps. The
2026 edition governs. No project source-specific errata file was found.

All declarations below are in
`Langlands.Algebra.NonUnitalModuleDualFixedPartMaps`. The named scalar
modules, opposite idempotent and nested-subtype constructors are derived
internal details making the original proof's maps precise. Their source
provenance is the passages above together with the already constructed
actual fixed parts, actual nondegenerate dual, and canonical scalar
adapters.

## The actual right fixed part and its scalars

`oppositeIdempotent e` is the idempotent whose value is
`MulOpposite.op (e : A)`. Its proof applies `op` to the original
idempotence equation; the reversed product has equal factors.
`oppositeIdempotent_val` and `oppositeIdempotent_mul_self` expose its
value and idempotence.

The local actions are explicitly `NonUnitalModuleDual.fullAction hA hM`
and `NonUnitalModuleDual.dualAction hA hM`. `RightFixedPart hA hM e`
is exactly

```text
NonUnitalModuleCorner.FixedPart (oppositeIdempotent e)
  (NonUnitalModuleDual.Dual hA hM).
```

The additive group is the published fixed-part additive group. The
ambient right action is the published dual action. The ambient full
dual uses exactly `NondegenerateScalars.complexModule hA hM` on `M`.
`rightFixedPart_eq_subtype` exposes the fixation equation in the actual
dual. `rightFixedPart_eq_nestedSubtype` also unfolds the inner subtype:
its value is an actual full-dual linear functional with a proof of
membership in `nondegeneratePart hA.op (FullDual hA hM)`, followed by
the equation fixing that dual element under `op e`.

`rightFixedModule hA hM e` explicitly installs the published
`dualModule hA hM` and `dual_smulCommClass hA hM`, then specializes
`NonUnitalModuleCorner.inheritedComplexModule`. The complete scalar
formula is

```text
c • φ = ⟨c • φ.val, smul_mem_fixedPart (oppositeIdempotent e) c φ⟩.
```

`rightFixedModule_smul` gives this equation with the exact ambient dual
module explicit. `rightFixedModule_smul_val` exposes the inner dual
value. `rightFixedModule_smul_functional` identifies the entire included
full-dual functional with `c • φ.val.val`, and
`rightFixedModule_smul_apply` evaluates it as `c • φ.val.val m`.
These equations are definitional and retain both subtype layers.

`rightFixedModule_eq_canonical` compares this inherited structure with
the fixed-part module recovered from the same original right action.
The proof uses `Module.ext'` to compare scalar operations. It applies
`congrArg` to the ambient operation in
`NonUnitalModuleDual.canonicalModule_eq_dualModule hA hM` and uses
subtype extensionality. This avoids rewriting a dependent commutation
proof and preserves the precise module structures.

`rightFixedPart_fixed_functional` applies subtype value to the outer
fixation equation. `rightFixedPart_fixed_apply` evaluates the resulting
full-functional equation, obtaining
`φ.val.val ((e : A) • m) = φ.val.val m`.

`ofFixedFull e ψ hψ` constructs the two actual subtype layers directly.
The opposite idempotent itself witnesses membership of `ψ` in the
nondegenerate part; subtype extensionality lifts the same fixation
equation to the outer layer. `ofFixedFull_eq` exposes this whole
constructor, including both membership proofs, and
`ofFixedFull_functional` identifies its entire included functional with
`ψ`.

## Restriction of the included functional

`restriction hA hM e` is a complex-linear map from `RightFixedPart` to
the actual `Module.Dual ℂ (FixedPart e M)`. Its type explicitly selects
`rightFixedModule hA hM e` and the named
`NonUnitalModuleCorner.complexModule hA hM e`. For each `φ`, its
whole functional is

```text
φ.val.val.comp (NonUnitalModuleCorner.inclusionLinear hA hM e).
```

`restriction_functional` states this equality with the precise
canonical ambient module explicit. The proof of linearity in `φ`
uses extensionality of linear functionals: addition and complex
scalars on all the dual and subtype layers are inherited pointwise.

`restriction_coe` states equality of the whole function underlying the
restriction map with that composition formula.
`restriction_function_coe` states equality of each resulting
functional's whole function with `fun x => φ.val.val x.val`.
`restriction_apply` gives the corresponding application formula.

## Extension through the idempotent projection

`extensionFunctional hA hM e` first constructs a complex-linear map
into the actual full dual of `M`. It sends `ell` to

```text
ell.comp (NonUnitalModuleCorner.projectionLinear hA hM e).
```

`extensionFunctional_eq_comp` gives the equality of entire linear
functionals, using the named canonical ambient and fixed-part modules.
`extensionFunctional_apply` evaluates it as `ell (projection e m)`.
Additivity and complex homogeneity again follow by extensionality and
the pointwise dual operations.

`extensionFunctional_fixed` proves that this full functional is fixed
under the actual action of `op e`. After linear-map extensionality, the
remaining equation compares `projection e ((e : A) • m)` with
`projection e m`. Subtype extensionality and the published
`NonUnitalModuleCorner.coordinate_idempotent e m` prove it.
`extensionFunctional_mem_dual` uses this equation and
`oppositeIdempotent e` as the explicit witness of membership in the
actual nondegenerate part.

`extension hA hM e` then applies `ofFixedFull` to obtain a complex-linear
map into the actual `RightFixedPart`. Its type names the same scalar
modules as restriction. Its additivity and homogeneity proofs apply
subtype extensionality twice and linear-functional extensionality
once. `extension_eq_nestedSubtype` exposes both subtype layers with
the actual membership and fixation proofs.

`extension_functional` identifies the whole included full-dual
functional with composition by `projectionLinear`.
`extension_coe` identifies the whole subtype-valued function
underlying extension. `extension_function_coe` gives the whole
function underlying each included full-dual functional, and
`extension_apply` states
`(extension hA hM e ell).val.val m = ell (projection e m)`.
The published projection has value `(e : A) • m`, as required by the
source formula.

## Universe interfaces and scope

The final public examples assign the complete unapplied declarations
`@RightFixedPart`, `@rightFixedModule`, `@restriction`, and `@extension`
to types quantified over independent `uA` and `uM`. The existing
scalar-adapter pair supplies the corresponding independent
`uA`, `uM`, `uN` interface for original intertwiners. No complex
structure on the original carrier is an additional hypothesis.
Arbitrary dimension, zero algebras and modules, and the zero
idempotent are all allowed. The original nonunital actions are retained,
including when the algebra has a global unit.

This construction pair supplies the data and formulas for the next
fixed-part duality statements. The inverse equations, isomorphism and
its whole-map naturality and right-corner compatibility, comparison
with full-dual fixed parts, exactness, bidual injection, I.4.2/I.4.3
comparisons, and admissible reflexivity remain separate successors.
