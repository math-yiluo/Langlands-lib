# Equal finite unit classes as subgroup membership (M358.007 proof)

This module proves the published proposition
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_eq_iff_div_memStatement`
as the theorem
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_eq_iff_div_mem`.

## Target

The theorem has the statement's complete telescope, in the same order and with
the same binder kinds: implicit `{K : Type u}`, instance-implicit
`[Field K]`, explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
explicit `n : ℕ` and explicit `a b : F.valuationSubringˣ`. Its type is the
fully applied proposition
`standardLubinTateUnitParameterClass_eq_iff_div_memStatement F n a b`.
No hypothesis is added. The field universe `u` and the second LocalField
universe `v` stay independent.

Let `U = CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)`, the
level-`n + 1` higher principal-unit subgroup of `F.valuationSubringˣ`. The
statement says that `standardLubinTateUnitParameterClass F n a` and
`standardLubinTateUnitParameterClass F n b` are equal if and only if
`a / b ∈ U`.

## Implemented proof

1. The imported definition `standardLubinTateUnitParameterClass F n` is
   `QuotientGroup.mk' U`, and its codomain
   `standardLubinTateUnitParameter F n` is `F.valuationSubringˣ ⧸ U`. The
   proof uses `change` to replace the goal by
   `QuotientGroup.mk' U a = QuotientGroup.mk' U b ↔ a / b ∈ U`. This only
   unfolds the statement and the class map. It is accepted by definitional
   unfolding. The right-hand side is unchanged.
2. Mathlib's `QuotientGroup.eq_iff_div_mem`
   (`Mathlib/GroupTheory/QuotientGroup/Defs.lean`) states
   `(x : G ⧸ N) = y ↔ x / y ∈ N` for a normal subgroup `N`. Mathlib's
   `QuotientGroup.mk'_apply` holds by `rfl`, so `QuotientGroup.mk' U a` is
   definitionally `(a : F.valuationSubringˣ ⧸ U)`. `exact` closes the goal
   with this lemma at `x = a`, `y = b` and `N = U`.
3. The normality argument is found by instance search. It is Mathlib's
   `Subgroup.normal_of_isMulCommutative U`. It applies because
   `F.valuationSubringˣ` is commutative: it is the unit group of a
   commutative ring. The class map `QuotientGroup.mk' U` in the imported
   Definitions pair also needs this normality.

The proof uses no finiteness of the quotient, no Lubin–Tate formal-module
action, no uniformizer, no chosen representative and no second local field
structure. It adds no instance, simp lemma or helper declaration.

## Checks

`lean_check` in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled
this module and the imported target module with no errors and no warnings.
The declaration inspection found a theorem with level parameters `[u, v]` and
exactly the axioms `propext`, `Classical.choice` and `Quot.sound`.
A separate private check module, not part of this submission, confirmed
three facts. First, after the binder telescope, the theorem type is
syntactically the constant
`standardLubinTateUnitParameterClass_eq_iff_div_memStatement.{u,v}` applied
to the bound variables. Second, its binder telescope with codomain `Prop`
equals the statement's own type. Third, instance search finds
`Subgroup.normal_of_isMulCommutative` for `U`.

## Source correspondence and imports

The original is Naganori Yamaguchi's
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`, unit M358.007
`LubinTate.standardLubinTateUnitParameterClass_eq_iff_div_mem`. The theorem
type is on lines 99–105 and the proof on lines 106–112. The file was read
in the registered snapshot and its SHA256 checked as
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
The proof here is the original proof: the same `change` to the
`QuotientGroup.mk'` form, followed by `exact QuotientGroup.eq_iff_div_mem`.
The only difference is that the `change` target writes the right-hand
side `a / b ∈ U` out instead of the original placeholder `_`, because the
goal before `change` is the folded statement.

| Original name | Name here |
| --- | --- |
| `LubinTate.standardLubinTateUnitParameterClass_eq_iff_div_mem` | `Langlands.NYLL.LubinTate.standardLubinTateUnitParameterClass_eq_iff_div_mem` (proof of `standardLubinTateUnitParameterClass_eq_iff_div_memStatement`) |

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.RepresentativeStatements`,
the unchanged published target pair. Through it come the unit parameter
Definitions pair, the shared LocalField and principal-unit filtration
definitions, and `Mathlib.GroupTheory.QuotientGroup.Defs`. No external
repository module is imported. No target, definition or imported pair is
edited.

## Attribution and modifications

The original source is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is kept verbatim. The existing,
unmodified [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) still apply. Their SHA256
values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 440 extracted this proof on 14 November 2026 and made these changes:

- added the `Langlands.NYLL` namespace prefix;
- stated the theorem type as the published proposition
  `standardLubinTateUnitParameterClass_eq_iff_div_memStatement F n a b`;
- wrote out the right-hand side in the `change` target;
- imported only the published target pair instead of the original module's
  imports;
- added the docstring line naming M358.007 and wrote this explanation.

Worker 298 published the target statement and the Definitions pair. The
proof here was written from the original source and did not reuse the
private development probe mentioned in the task context. The approved
environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
