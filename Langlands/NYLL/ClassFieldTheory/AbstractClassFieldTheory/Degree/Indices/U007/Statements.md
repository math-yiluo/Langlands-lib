# NYLL M006.007–009: saturation relative-index targets

The paired Lean file defines three proposition targets from Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.
The entire original file was read; its SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
No applicable source erratum was found in the current Library.

All source names below belong to `ClassFormation`. All adapted names
belong to `Langlands.NYLL.ClassFormation`.

| Source unit and lines | Original name | Adapted name |
| --- | --- | --- |
| M006.007, lines 91–98; signature 93–96 | `relIndex_saturation_eq_inf_ker_relIndex` | `relIndex_saturation_eq_inf_ker_relIndexStatement` |
| M006.008, lines 100–108; signature 102–105 | `map_relIndex_eq_saturation_relIndex` | `map_relIndex_eq_saturation_relIndexStatement` |
| M006.009, lines 110–122; signature 114–117 | `relIndex_eq_map_relIndex_mul_inf_ker_relIndex` | `relIndex_eq_map_relIndex_mul_inf_ker_relIndexStatement` |

The complete section telescope at source lines 23–25 is preserved:
independent universes `u v`, implicit `{G : Type u}` and `{D : Type v}`,
then `[Group G]` and `[Group D]`. Each declaration then takes explicit
`d : G →* D`. M006.007 and M006.009 take implicit
`{L K : Subgroup G}` followed by explicit `hLK : L ≤ K`. This inclusion
hypothesis remains a parameter even though it does not occur in the
equality itself. M006.008 instead takes explicit `(L K : Subgroup G)`
and has no inclusion hypothesis.

For M006.007 the target is

```lean
L.relIndex (K ⊓ (L ⊔ d.ker)) =
  (L ⊓ d.ker).relIndex (K ⊓ d.ker)
```

Thus the index of `L` in the kernel-saturated part of `K` agrees with
the index of the kernel intersections. For M006.008 the target is

```lean
(L.map d).relIndex (K.map d) =
  (K ⊓ (L ⊔ d.ker)).relIndex K
```

For arbitrary `L` and `K`, the relative index of their images equals
the index in `K` of its intersection with `L ⊔ d.ker`. For M006.009
the target is

```lean
L.relIndex K =
  (L.map d).relIndex (K.map d) * (L ⊓ d.ker).relIndex (K ⊓ d.ker)
```

This is the image–kernel factorization for the inclusion `L ≤ K`,
with the image factor first, exactly as in the source. These are
Mathlib's natural-valued `Subgroup.relIndex` expressions. Infinite
relative indices have value zero. There is no finiteness,
commutativity, subgroup normality or surjectivity hypothesis.

Worker 190 made the following modifications: extracted only the three
source signatures; prefixed the namespace; appended `Statement` to
each name; replaced each theorem and its proof with a `def` whose
`Prop` body is the source conclusion; changed the docstrings to
describe targets; replaced the original
`Nyll.GaloisCohomology.GroupTheory.QuotientTower` import by
`Mathlib.GroupTheory.Index`; and omitted the unused
`open scoped Pointwise`. No mathematical expression, universe,
parameter order, binder kind or hypothesis is changed. No instance,
helper definition or proof is added.

The targets reuse Mathlib's `Subgroup.relIndex`, `Subgroup.map`,
`MonoidHom.ker` and subgroup lattice operations by Lean name.
The published
`Langlands.NYLL.ClassFormation.kernelCosetEquivSaturation`
from `Indices.U006.Definitions` corresponds to source M006.006 and is
used in the original proof of M006.007; it does not occur in these
statement bodies. The original proof of M006.008 uses
`Subgroup.relIndex_comap`, `Subgroup.comap_map_eq` and
`Subgroup.inf_relIndex_right`. The proof of M006.009 uses M006.007,
M006.008 and `Subgroup.relIndex_mul_relIndex`. None of those proof
dependencies is required to state the targets. Exact-name searches
in the Library and the focused Mathlib index source found no existing
declarations with these three names; this contribution supplies the
required targets rather than claiming reuse of an entire theorem.

The focused module compiles in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`; each of the three declarations
was individually inspected with `statement_returns_prop: true`.
A private probe mechanically extracts the source signatures under their
complete original section telescope and checks equality of each whole,
unapplied source-target constant with its adapted constant by `rfl`,
with explicit independent universes. It also reconstructs the original
three proofs using the published M006.006 equivalence and assigns each
unapplied source theorem to its complete adapted target type.
The probe compiles. The initial target build emits only the expected
unused-variable warnings for the retained `hLK` names in M006.007 and
M006.009. These checks are development evidence and do not publish proofs
or replace independent semantic review.

The original copyright, Apache-2.0 release and author header are retained
in the Lean file. The Library's `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are retained unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively.

These are unproved proposition definitions. Their proofs are separate
work. This contribution supplies no host class-formation, cup,
transfer, Tate or reciprocity result.
