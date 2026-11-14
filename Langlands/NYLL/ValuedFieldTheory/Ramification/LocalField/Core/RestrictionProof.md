# Exact NYLL M327.009 proof

The theorem
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_map_restrict`
proves exactly the Library proposition
`Langlands.NYLL.RamificationTheory.LocalField.localUpperRamificationGroup_map_restrictStatement`,
imported from `LocalField.Core.RestrictionStatement`. That closed target has
`K : Type` with the published nonarchimedean local-field hypotheses,
`E F : IntermediateField K (SeparableClosure K)`, hEF : E <= F,
finite-dimensional and Galois hypotheses for both fields, and every real t.
It identifies the image of the actual chosen-extension upper group of F
under the published `intermediateFieldRestrictNormalHom E F hEF` with the
actual upper group of E. No additional premise is introduced.

## Implemented proof

The module `FixedFieldTransport` proves the arbitrary-real fixed-field
restriction identity from the published FLT quotient theorem. Its helper
module `FLTComparison` checks the relation between NYLL's real-indexed groups
and FLT's rational-indexed groups. Their paired Markdown describes the
implemented arguments, including finite residue and all quotient hypotheses.

The final assembly here follows the intermediate-field portion of the pinned
NYLL proof. Set `EF := E.comap F.val`, the copy of E inside F, and construct
the K-algebra equivalence `eEF : EF ≃ₐ[K] E` using hEF. Galoisness transfers
along this equivalence. Let H be EF's fixing subgroup. It is normal, and the
Galois correspondence gives
`eFixed : IntermediateField.fixedField H ≃ₐ[K] E`.

The published `intermediateFieldRestrictNormalHom_apply_val` and Mathlib
`AlgEquiv.restrictNormal_commutes` show that the requested homomorphism is
the composition of actual normal restriction from F to the fixed field
and conjugacy by eFixed. `Subgroup.map_map` then reduces the conclusion to
`PortInternal.FltBridge.local_map_fixed` followed by the published
`localUpperRamificationGroup_map_autCongr`. The latter is the separate exact
M327.006 proof; this file imports it rather than reproducing its proof.

## Source correspondence and changes

Source: Naganori Yamaguchi, *ClassFieldTheory*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean:610–733`, M327.009.
The section parameters remain `Type`, the whole closed target telescope is
retained, and the conclusion uses the unchanged published M259.001 map.
The `EF`, `eEF`, H and `eFixed` assembly corresponds to source lines 622–657;
the factorization is the counterpart of source lines 680–698.

Worker 296 replaces the original M326 quotient and fixed-field-upper-group
route by the compiled derived FLT comparison in the two helper modules.
The final composition therefore needs neither the source's quotient-image
comap cancellation nor its separate fixed-field-upper-group identification.
The source's obsolete `MonoidHom.coe_ofClass` simplifier is omitted for the
pinned Mathlib version. Namespaces and imports are adapted to the Library.
All extension/action instances in the helpers are local; no new global
valuation extension instance or axiom is introduced. NYLL attribution and
Apache-2.0 notices remain in `licenses/NYLL/`; FLT notices remain in
`licenses/Anthropic-FLT/`.

The mathematical dependencies of this module are the two helper modules,
the exact M327.006 algebra-equivalence transport theorem, and the published
M259 intermediate-field restriction laws. The target statement and those
imported interfaces are unchanged.
