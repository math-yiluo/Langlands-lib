# NYLL M101.006: compatibility of the two fixed-unit carrier equivalences

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquivStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquiv`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractRelativeUnitsEquiv_extensionUnitsEquivStatement k Ω K L hLK hnormal x`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits.Representation.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, the explicit fields `k Ω : Type` with
instances `[Field k] [Field Ω] [Algebra k Ω]` (the section's
`[IsGalois k Ω]` is omitted, as in the source and the statement), closed
subgroups `K L : ClosedSubgroup (Gal(Ω/k))`, the containment
`hLK : L.toSubgroup ≤ K.toSubgroup`, the explicit normality hypothesis
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal` and an element `x`
of the carrier
`(extensionFixedRepresentation (galoisAmbientUnitsRep k Ω) K L hLK hnormal).V`
of the descended representation of `G_K / G_L` on the units of `Ω` fixed by
`G_L`. It has no universe parameters.

Unfolding the published proposition gives

```lean
abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
    (abstractExtensionFixedRepresentationUnitsEquiv
      k Ω K L hLK hnormal x) =
  extensionFixedRepresentationEquiv
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal x
```

that is, sending `x` to the units of the upper fixed field by the carrier
comparison and then identifying those units with the fixed coefficients
`A_L` gives the fixed-carrier equivalence of the extension representation
applied to `x`.

## Implemented proof

The complete proof body is

```lean
  exact (abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK).apply_symm_apply
      (extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x)
```

Write `e := extensionFixedRepresentationEquiv (galoisAmbientUnitsRep k Ω) K L hLK hnormal`
and `f := abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK`.
The published definition
`abstractExtensionFixedRepresentationUnitsEquiv k Ω K L hLK hnormal` is the
additive equivalence `e.trans f.symm`, so its value at `x` is definitionally
`f.symm (e x)`. The left side of the goal is therefore definitionally
`f (f.symm (e x))`, and Mathlib's `AddEquiv.apply_symm_apply f (e x)`, of
type `f (f.symm (e x)) = e x`, closes it; `exact` accepts this term up to the
definitional unfolding of the statement definition and of `AddEquiv.trans`.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring, the `@[simp]`
attribute of source line 132 and the `omit [IsGalois k Ω] in` of line 130.
No auxiliary declaration, extra hypothesis or instance is introduced. The
development check reports no errors or warnings and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeUnitsEquiv_extensionUnitsEquivStatement`
  in AbstractFixedFieldUnits.Representation.Statements.
- The published definition
  `Langlands.NYLL.LocalClassFieldTheory.abstractExtensionFixedRepresentationUnitsEquiv`
  (AbstractFixedFieldUnits.Representation.Definitions), unfolded
  definitionally.
- The published definitions
  `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixedFieldUnitsEquivGaloisFixed`
  (AbstractFixedFieldUnits.Relative.Definitions) and
  `Langlands.NYLL.ClassFormation.extensionFixedRepresentationEquiv`
  (AbstractClassFieldTheory.Reciprocity.FieldRepresentation.FixedCarrier.Definitions),
  used only as the equivalences `f` and `e` above, together with the
  definitions they mention (`galoisAmbientUnitsRep`,
  `abstractRelativeFixedField`, `extensionFixedRepresentation`), all reached
  through the Statements module's imports.
- Mathlib's `AddEquiv.apply_symm_apply` and `AddEquiv.trans`.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:130–147`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean#L130-L147).
Line 130 is `omit [IsGalois k Ω] in`, 131 the docstring, 132 the `@[simp]`
attribute, 133–143 the signature and 144–147 the proof. The section variable
line 36 is
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, inside
`namespace LocalClassFieldTheory` (line 23) with
`open RamificationTheory CyclicCohomology KummerTheory` (line 24),
`open LocalFieldTheory` (26), `open ClassFormation` (28),
`noncomputable section` (32) and `open CategoryTheory` (34). The source
writes the normality hypothesis as `(extensionSubgroup K L hLK).Normal`,
which the published statement and this theorem write with its definitional
body `L.toSubgroup.subgroupOf K.toSubgroup`. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m101)
places this proof at M101.006 (source unit start line 133). The whole-file
SHA-256 is
`9a2d82d81f9f00269a7f9904e005ab931bbde64ea62cbe8fe7327d7b31a017f1`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `abstractRelativeUnitsEquiv_extensionUnitsEquiv` (M101.006) | Published `abstractRelativeUnitsEquiv_extensionUnitsEquivStatement` in AbstractFixedFieldUnits.Representation.Statements |
| Proof `abstractRelativeUnitsEquiv_extensionUnitsEquiv` | This theorem of the same adapted name in AbstractFixedFieldUnits.Representation.U006.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, merges the source's
namespace openings into one line and omits the unused `open LocalFieldTheory`
and `open CategoryTheory`, keeps the `noncomputable section`, the section
variables, `omit [IsGalois k Ω] in`, the docstring and `@[simp]`, writes the
normality binder with the body of `extensionSubgroup` as the published
statement does, and states the theorem's type as the published proposition
applied to `k Ω K L hLK hnormal x`. The proof is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M101.006. The quotient-representative, coset-action
and representation-isomorphism units M101.007–M101.010 and any host
class-formation, cup, transfer, Tate or reciprocity target are separate work.
