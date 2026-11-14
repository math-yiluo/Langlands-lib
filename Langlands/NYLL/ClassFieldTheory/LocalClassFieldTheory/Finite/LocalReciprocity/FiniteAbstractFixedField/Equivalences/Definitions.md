# Abstract relative quotients and concrete Galois groups

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.016 | `abstractExtensionQuotientEquivAmbient` (256–277) | `abstractExtensionQuotientEquivAmbient` |
| M099.017 | `abstractExtensionQuotientEquivGaloisGroup` (279–302) | `abstractExtensionQuotientEquivGaloisGroup` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the source namespace with `Langlands.NYLL` and replace the broad
source imports with the published M099.014 kernel and M099.015 surjectivity proof
modules and the focused closed-fixing-subgroup definition module. Retain both
complete data constructions and all proof terms. The source
section variables at line 31 are explicit `k Ω : Type` (both Type 0), followed by
`[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`; each declaration then has
explicit `K L`, `hLK` and `hnormal`, in that order. Both constructions use the
Galois instance and retain it. Omit unused source namespace openings. No global
instance is introduced.

M099.016 identifies the quotient of the actual subgroup `K.toSubgroup`
by `L` regarded inside `K` with the quotient of
`Gal(Ω/abstractFixedField k Ω K)` by the fixing subgroup of the actual upper
relative fixed field. Its construction transports along the published exact
kernel equality using `QuotientGroup.quotientMulEquivOfEq`, then uses
`QuotientGroup.quotientKerEquivOfSurjective` and the published surjectivity
theorem. The complete source bodies use the published proof names
`abstractRelativeToAmbientQuotient_ker` and
`abstractRelativeToAmbientQuotient_surjective`; no source proof is inlined.

M099.017 composes M099.016 with `InfiniteGalois.normalAutEquivQuotient` for the
actual closed fixing subgroup, and with `AlgEquiv.autCongr` of
`IntermediateField.equivOfEq` for `InfiniteGalois.fixedField_fixingSubgroup`.
Its target is the actual relative Galois group of the upper concrete field over
the lower concrete field. The local normality instances and the source proof
term establishing normality of the closed fixing subgroup are retained.

In both declarations, the original `CyclicCohomology.extensionSubgroup K L hLK`
is written as its exact body `L.toSubgroup.subgroupOf K.toSubgroup`, following
the published prerequisite units. This is the body of source M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`, and ignores the
inclusion proof. M099.016's result-type normality `letI` has the explicit type
`(abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal`, since the
published theorem returns the definitionally equal `...Statement` alias. The
annotation registers the same proof term as the required class; it changes
neither quotient nor equivalence. The source already uses this annotation in
the bodies.

The whole original M099 file has SHA-256
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`.
The two declaration signatures and bodies occupy lines 259–277 and 281–302,
preceded by the docstrings included in the table. These units are necessary
data prerequisites for the M101 unit-action targets. They introduce neither
finite-index nor local-field assumptions. Private development probes compare
each unapplied adapted constant with the complete source construction by `rfl`;
independent semantic acceptance remains separate.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.
