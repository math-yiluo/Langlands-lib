# Cardinality of the actual unramified norm quotient: proposition target

`Langlands.NYLL.PortInternal.M267.d008Statement` is the closed proposition
that a finite unramified Galois extension of nonarchimedean local fields
`K L : Type` satisfies
`Nat.card (Langlands.NYLL.LocalFieldTheory.NormQuotient K L) = Module.finrank K L`.
The quotient is the published quotient of `Kˣ` by the image of the actual field
norm on `Lˣ`. No replacement norm map or assumed cardinality equality is used.
This is a target definition; its proof remains a separate obligation.

The entire source section telescope is retained in order: both fields are at
universe zero, each has `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances; then come `Algebra K L`,
`FiniteDimensional K L`, `IsGalois K L`, the valuation-extension instance,
`IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, and the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L`.
There is no extra `Finite (NormQuotient K L)` hypothesis. As in the source,
`Nat.card` itself does not require such an instance in the target.

## Source correspondence and changes

The original is the private theorem
`LocalClassFieldTheory.normQuotient_card_eq_finrank` (M267.008), lines 117–129,
with section parameters at lines 34–44, in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`,
Naganori Yamaguchi's ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The full original module was read; its SHA-256 is
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
It belongs to registered source `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/` followed by that path.
No applicable project errata entry was found.

The published declaration inventory `notes/reuse/nyll-public-port/m263-m269.md`
assigns the private original the stable public internal name
`Langlands.NYLL.PortInternal.M267.d008`; this target adds `Statement`.
Worker 205 universally closed the original telescope, changed the theorem
into a `def ... : Prop`, and omitted its proof. The conclusion is unchanged.
The target is needed for the source route proving injectivity of the comparison
between the actual norm quotient and the valuation quotient (M267.009).

The imports reuse `NormQuotient.U002.Definitions` and
`FiniteUnramified.Definitions`, plus Mathlib Galois and finite-cardinal support.
The local reciprocity equivalence and the cyclic Galois-group equivalence used
by the original proof are not needed to state the proposition. No local or
global instance is introduced.

The original copyright and author header is retained, with an explicit
modification record. Apache-2.0 license and notices remain in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No other worker's draft
or earlier adaptation of this target was reused.

## Development check

A focused `lean_check` compiled this module with no errors or warnings and
inspected `Langlands.NYLL.PortInternal.M267.d008Statement` as a definition
with `statement_returns_prop: true` and no universe parameters. The successful
check uses only the two published data modules and Mathlib imports named above.
It supplies no proof or independent semantic acceptance of the target.
