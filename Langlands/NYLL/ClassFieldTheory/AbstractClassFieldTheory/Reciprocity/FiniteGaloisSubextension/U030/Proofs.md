# NYLL M040.030: the left compositum bound

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.compositum_le_left`
proves exactly the published target `compositum_le_leftStatement L₁ L₂`.
It retains the source parameters: arbitrary universe `u`, a group `G : Type u`
with a topological space, a closed subgroup `K`, and finite Galois
subextensions `L₁ L₂` of `K`. The conclusion is
`(L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup`.

The implemented proof is the source term `inf_le_left`. The published
`compositum` definition has field `L₁.field ⊓ L₂.field`; its underlying
subgroup is definitionally the intersection. Unfolding the named target
therefore makes the required inequality the left projection from that
intersection. No additional topological, normality or finiteness hypothesis
is introduced. The sole direct project import is the existing
`FiniteGaloisSubextension.Statements` module; the proof uses its published
`compositum` definition and Mathlib's lattice lemma `inf_le_left`.

The source is Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`,
lines 401–404; the surrounding group-only context is at lines 27–46.
The file SHA-256 is
`c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 242 extracted this single theorem, changed the namespace prefix from
`ClassFormation` to `Langlands.NYLL.ClassFormation`, replaced the broad source
import with the focused published statement import, and wrote the result as
an application of the unchanged Prop-valued target. The original proof term
and parameter order are unchanged. The unused source namespace openings,
`noncomputable section`, and section scaffolding are omitted. The original
copyright and author header is retained under Apache-2.0; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

This theorem concerns the abstract closed-subgroup model of finite Galois
subextensions. It makes no host class-formation or reciprocity assertion.
