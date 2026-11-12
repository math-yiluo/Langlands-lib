# Proper morphisms under a change of base scheme

`ProperSchemeBaseChangeStatement` states that for arbitrary schemes `S`, `T`,
an arbitrary morphism `g : T → S`, algebraic spaces `X`, `Y` over `S`, and a
proper morphism `f : X → Y`, the actual base-changed morphism
`baseChangeMap g f` over `T` is proper. The common universe is arbitrary.
No representability, separatedness of the base schemes or finite-type
assumption on the base morphism is imposed.

The source is the Stacks Project, *Morphisms of Algebraic Spaces*, version
ed88ff78, Lemma 40.3, Tag 04WP, printed p.81: proper morphisms are stable under
base change. The registered source is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`; its chapter PDF has
SHA-256 `46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.
This statement is the specialization to a change of the ambient base scheme,
expressed with the Library's restriction construction `baseChangeMap`.

`IsProperMorphism` is the published conjunction of separatedness,
quasi-compactness, local finite type and universal closedness, as in Stacks
Definition 40.1, Tag 03ZM, printed p.80. The imported
`SpaceMorphismBaseChange` already preserves separatedness and local finite
type. Preservation of the quasi-compact and universally closed components
remains part of the proof obligation; relevant source results are Lemma 8.4,
Tag 03HF, printed p.13, and Lemma 9.3, Tag 03IS, printed p.15.

This file supplies the proposition only. It does not prove the preservation
theorem or any adelic properness statement.
