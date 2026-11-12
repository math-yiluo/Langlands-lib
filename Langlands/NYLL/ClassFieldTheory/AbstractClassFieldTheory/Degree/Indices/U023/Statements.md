# NYLL M006.023–025: cardinal image–kernel targets

The paired Lean file states the image, kernel and combined cardinal-index
identities of Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.
The source file SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

The complete source section (lines 23–25) gives independent universes
`u v`, implicit `G : Type u`, `D : Type v`, `[Group G]` and
`[Group D]`. Each target retains all of these parameters in that order.
Neither normality of the subgroups nor finiteness of any coset space
is assumed.

| Source unit and location | Adapted declaration after `Langlands.NYLL.ClassFormation.` | Explicit parameters after the shared section |
| --- | --- | --- |
| M006.023, lines 247–254, signature 249–253 | `intersectionIndexCardinal_image_eq_saturationStatement` | `d : G →* D`, `L K : Subgroup G` |
| M006.024, lines 256–265, signature 258–264 | `relativeIndexCardinal_kernel_eq_saturationStatement` | `d : G →* D`, then implicit `L K : Subgroup G`, and explicit `hLK : L ≤ K` |
| M006.025, lines 267–312, signature 270–277 | `relativeIndexCardinal_eq_map_mul_inf_kerStatement` | `d : G →* D`, then implicit `L K : Subgroup G`, and explicit `hLK : L ≤ K` |

M006.023 identifies the intersection index of `L.map d` in `K.map d`
with that of `K ⊓ (L ⊔ d.ker)` in `K`. The target preserves the
source's left lift `Cardinal.lift.{u}` from `Cardinal.{v}` and right
lift `Cardinal.lift.{v}` from `Cardinal.{u}`. Both sides consequently
lie in `Cardinal.{max u v}`, with independent source and image universes.
Here `intersectionIndexCardinal` is defined for arbitrary `L,K`,
so M006.023 has no containment hypothesis.

M006.024 equates the relative index of
`L ⊓ d.ker ≤ K ⊓ d.ker` with the relative index of
`L ≤ K ⊓ (L ⊔ d.ker)`. It uses the exact source inclusion proofs.
Both cardinalities lie in `Cardinal.{u}` and require no lifts.
M006.025 equates the lift of the relative index of `L ≤ K` with the
product of the lifted relative indices of the image inclusion and the
kernel-intersection inclusion, in that order. It retains every source
`Cardinal.lift` universe annotation and `Subgroup.map_mono` argument.
All three targets concern actual coset cardinalities, including infinite
values.

The existing `Langlands.NYLL.ClassFormation.intersectionIndexCardinal`
and `relativeIndexCardinal` are reused from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U010.Definitions`.
They correspond to source M006.010–011 (lines 131–141).
Worker 120 extracted the three theorem signatures, prefixed their
namespace, appended `Statement`, and made the conclusions the bodies
of definitions returning `Prop`. The original broad import is replaced
by that published data module and `Mathlib.Algebra.Group.Subgroup.Ker`.
No source parameters, hypotheses,
lifts or inclusion proofs are changed. No new instances or proofs are
introduced.

A private probe reproduces the complete original module with its
namespace adapted and its quotient-tower import and reference changed
to the published
`Langlands.NYLL.Subgroup.quotientTowerEquiv`.
Assignments of the source theorems to the complete adapted targets,
at independent universes `u v`, check their types and conclusions.
The entire original and published cardinal-data constants also agree by
`rfl`. The focused module compiles and every target is inspected as
returning `Prop` in environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`.
This establishes that the private source equivalences M006.015–022,
the kernel equivalence M006.006 and the tower law M006.014 are not
needed to state these targets. Their constructions or results may still
be required in the separate proofs.

This contribution leaves all three targets unproved. It does not assert
local reciprocity or any host class-formation, transfer or Tate theorem.

The original copyright, Apache-2.0 release and author header are retained.
The retained files are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
