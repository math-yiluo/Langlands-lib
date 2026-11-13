# Successive principal-unit quotient data (M132.001–005)

For any `K : Type u`, `[Field K]`, supplied `[ValuativeRel K]`, and `n : Nat`,
this module constructs the actual quotient group
`principalUnits K n ⧸ (principalUnits K (n + 1)).subgroupOf (principalUnits K n)`.
The subgroup and the integer-ring units are the published NYLL and canonical
Mathlib constructions. No positivity, topology or local-field premise is added.

The complete source-to-Library map is below. Every adapted name has prefix
`Langlands.NYLL.LocalFieldTheory.`; each original has prefix `LocalFieldTheory.`.

| Unit | Source lines | Original and adapted suffix | Meaning |
| --- | --- | --- | --- |
| M132.001 | 28–30 | `PrincipalUnitsSuccQuot` | Actual quotient type in universe `u` |
| M132.002 | 34–41 | `principalUnitsSuccQuotCommGroup` | Canonical commutative quotient-group instance |
| M132.003 | 43–53 | `principalUnitsSuccQuotConcreteEquiv` | Multiplicative reflexive equivalence with the quotient representation |
| M132.004 | 56–62 | `principalUnitsSuccQuotMk` | Canonical quotient monoid homomorphism |
| M132.005 | 65–75 | `principalUnitsSuccQuotLift` | Canonical lift of a homomorphism killing the successor subgroup |

The first four telescopes are `(K : Type u) [Field K] [ValuativeRel K] (n : Nat)`.
The lift keeps `{K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]`,
then `(n : Nat)`, `(f : principalUnits K n →* M)`, and the explicit containment
`h : (principalUnits K (n + 1)).subgroupOf (principalUnits K n) ≤ f.ker`,
in exactly that order. The codomain universe remains independent. Its value
is `PrincipalUnitsSuccQuot K n →* M`.

All five declaration bodies, including all `change`, `infer_instance`,
`MulEquiv.refl`, `QuotientGroup.mk'` and `QuotientGroup.lift` terms, are copied
unchanged. The named group instance exposes the canonical structure of this
new quotient type and does not replace an existing Mathlib or Library instance.
The published principal-unit definition and Mathlib's quotient constructors
are reused by name. No separate quotient model or assumed equivalence is used.

The modifications are the namespace prefix and the import reduction to
`PrincipalUnits.Definitions` and `Mathlib.GroupTheory.QuotientGroup.Basic`.
The source's `Mathlib.SetTheory.Cardinal.Finite`, `Mathlib.RingTheory.Filtration`
and broad `PrincipalUnits` imports are unnecessary here. Source namespace,
noncomputable section, universe `u`, notation scope and `open Filter` are retained.
Documentation is restricted to this extraction. No theorem command is copied.
This module supplies no host reciprocity or principal-unit comparison result.

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitQuotients.lean`.
The complete source file SHA-256 is
`6147c6613cd0176ace8787d7c65a3026d23bd5e23dc3282902d5ea66a0977c83`.
Its readable retained copy is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata notes.

The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 211 performed this extraction and namespace adaptation. No patch10 edit
or other worker's implementation draft was used.
