# NYLL M024: relative norm evaluation statement target

The paired Lean file adapts one theorem statement from Naganori Yamaguchi's
ClassFieldTheory at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`,
SHA-256
`5d57e3b5f1941fc987fefea159ad4686bb5f934319d6662c436b917bdbbf8578`.
The source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the available project notes.

## Source correspondence

| Unit | Source name | Statement lines | Original proof line | Adapted Prop definition |
| --- | --- | --- | --- | --- |
| M024.010 | `ClassFormation.relativeNorm_apply_coe` | 163–171 (docstring 163, `@[simp]` 164) | 172 | `Langlands.NYLL.ClassFormation.relativeNorm_apply_coeStatement` |

The enclosing source context is namespace `ClassFormation` (line 22),
the two namespace openings (lines 24–25), `noncomputable section`
(line 29) and the group variables at line 34. The theorem becomes a `def`
returning `Prop` whose body is precisely the original assertion after the
namespace change and abbreviation expansion described below. The original
proof (`rfl`) is a separate obligation.

## Complete parameters and assertion

The telescope is implicit `{G : IntegralRepGroupType}`, then `[Group G]` and
`[TopologicalSpace G]`, then explicit `A : Rep ℤ G`,
`K L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.toSubgroup`, then the
instance `[Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]`,
then explicit `a : ambientFixedAddSubgroup A L`, in that order, exactly as
in the source. `Langlands.NYLL.IntegralRepGroupType` is `Type 0`; the
representation carrier has an arbitrary universe, giving the declaration one
universe parameter. There is no normality, topological-group or continuity
assumption.

The assertion is

```lean
((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
  relativeNormValue A K L hLK a
```

that is, the underlying element of `A.V` of the relative norm of `a` (the
homomorphism `relativeNorm` of [`Definitions.md`](Definitions.md), M024.009)
equals the coset-sum norm value `relativeNormValue` (M024.005), the sum over
the actual finite relative quotient of the coset actions on `a`.

## Reused objects and modifications

The imported module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions`
supplies `relativeNorm`; through it the published M024 data module supplies
`relativeNormValue`, and M023.001 supplies
`Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`.

Source `CyclicCohomology.extensionSubgroup K L hLK` (M004.002,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54, SHA-256
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`) is an
abbreviation whose body is `L.toSubgroup.subgroupOf K.toSubgroup`; it is
expanded to that exact Mathlib `Subgroup.subgroupOf` term in the finite
instance, as in the published M024 statement module. The inclusion parameter
`hLK` remains in the telescope.

Worker 96 made only the following adaptations on 14 November 2026:

1. Prefix the namespace by `Langlands.NYLL` and import the focused relative
   norm module instead of the original imports. Drop the unused
   `open CyclicCohomology` and `open scoped BigOperators`.
2. Expand `extensionSubgroup` by its exact body, with parentheses.
3. Convert the theorem into the listed Prop-valued `def` with the
   `Statement` suffix, keeping the source hypotheses, binder kinds and order
   and the entire assertion. Omit the proof and the `@[simp]` attribute,
   which belongs to a proved equation.
4. Keep `noncomputable section`, replace the module introduction with an
   extraction notice, and mark the docstring as a target.

No instance or helper declaration is introduced.

## Development verification and scope

The module compiles with zero errors and warnings in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean v4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Focused inspection of
`relativeNorm_apply_coeStatement` succeeds and reports
`statement_returns_prop = true`.

A private probe reconstructs the source assertion with the original
`extensionSubgroup` abbreviation in the finite instance and verifies
`@relativeNorm_apply_coeSrc.{u} = @relativeNorm_apply_coeStatement.{u}` by
`rfl` for an arbitrary carrier universe, comparing entire dependent
functions. The probe supplies no public declaration.

This is a statement target in the NYLL abstract-field model; its proof
belongs to a separate `lean.proof@1` task after publication. The host
class-formation, cup, transfer, Tate and reciprocity obligations remain with
their existing owners.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim.
The existing Library files `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The Lean modification notice and this Markdown identify every adaptation.
