# Krull continuity of automorphism conjugation: M001.001 proof

`Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongr` proves
exactly the published proposition
`Langlands.NYLL.AlgebraicNumberTheory.continuous_algEquiv_autCongrStatement e`.
The implicit fields `F`, `E` and `E'` have independent universes; their three
`Field` instances, two `Algebra` instances and explicit `e : E ≃ₐ[F] E'`
retain the original order. No algebraicity, separability, normality or
finite-dimensionality of either extension is assumed. The automorphism groups
carry the canonical Mathlib Krull topologies.

## Implemented proof and dependencies

The sole direct import is the unchanged published statement module
`Langlands.NYLL.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding.U001.Statements`.
It imports `Mathlib.FieldTheory.KrullTopology`. No new instances, helper
statements or definitions are introduced.

The proof unfolds the target and uses `continuous_of_continuousAt_one` for
the group homomorphism `AlgEquiv.autCongr e`. Given a neighborhood `s` of the
identity in the target group, `krullTopology_mem_nhds_one_iff` supplies a
finite-dimensional intermediate field `M` of `E'/F` whose fixing subgroup is
contained in `s`. Put `N = M.map e.symm.toAlgHom`. The algebra equivalence
`M.equivMap e.symm.toAlgHom` gives a linear equivalence from `M` to `N`, so
`N/F` is finite-dimensional too. The same neighborhood criterion reduces the
remaining goal to inclusion of the fixing subgroup of `N` in the preimage
of `s`.

If `σ` fixes `N` and `x ∈ M`, then `e.symm x ∈ N`, hence
`e (σ (e.symm x)) = x`. The pointwise criterion
`IntermediateField.mem_fixingSubgroup_iff` therefore shows that
`AlgEquiv.autCongr e σ` fixes `M`, proving the inclusion. This argument uses
finite-dimensional subextensions only; it places no finiteness assumption
on the ambient fields.

## Source correspondence and attribution

The proof is adapted directly from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean`,
lines 28–57, theorem `AlgebraicNumberTheory.continuous_algEquiv_autCongr`.
The source signature is at lines 28–33 and proof at lines 33–57. The inventory
locator ending at line 54 stops inside the proof. The complete source file was
read; its SHA-256 is
`40b9e61892ae3b770967cee9c5d95bd41c2d0357909af82ab0e38a8a527be77f`.
The readable original is
[SeparableClosureEmbedding.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean>).

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Worker 168 retained the original proof route and body after adding a `change`
to unfold the target proposition. The theorem has the prescribed
`Langlands.NYLL` name, imports its published statement rather than the
original file's three Mathlib imports, and omits the unrelated separable-closure
constructions. The target and its dependencies are unchanged. No compatibility
patch or other worker's draft was reused. The related Library theorem
`Langlands.LocalGalois.semilinearAutCongr_continuous` assumes algebraicity
and is not used here.

The original copyright, author and Apache-2.0 license header is preserved;
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
This result supplies the NYLL support theorem M001.001; it does not prove a
host reciprocity, class-formation or cohomological comparison statement.

## Development validation

Lean service check `615cac9e-210d-4512-ab39-f35e80bf719e` compiled this
module in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`)
with no errors or warnings. Declaration inspection reports a theorem with
three independent universe parameters and only `propext`, `Classical.choice`
and `Quot.sound` as axioms. This development compilation is separate from
the candidate's exact-target validation and independent semantic review.
