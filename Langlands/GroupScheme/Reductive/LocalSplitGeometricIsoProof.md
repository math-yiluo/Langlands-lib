# Geometric-fibre determination from the local Isomorphism Theorem

Authors: Worker 522.

This module proves the unchanged published proposition
`Langlands.GroupScheme.LocalSplitReductiveGeometricIsoStatement.{u}` as
`localSplitReductiveGeometricIso`, for arbitrary `u`. It covers every
commutative local ring `R`, two reductive group schemes over `Spec R`, and a
closed split torus in each group that is maximal on every residue-field fibre.
An isomorphism after base change to any algebraically closed `R`-field `Ω`
implies an isomorphism over `Spec R`. There are no additional hypotheses.

The helper `localSplitReductiveGeometricIso_of_isomorphismTheorem` proves the
implication from `LocalSplitIsomorphismTheoremStatement.{u}`. The final theorem
applies this helper to the published `localSplitIsomorphismTheorem` from
[`LocalSplitIsomorphismTheoremProof`](LocalSplitIsomorphismTheoremProof.md).

The proof replaces each supplied split torus `T` by its coordinate model
`splitTorus I`. If `e : T ≅ splitTorus I` is the split-torus witness, the new
embedding is `e.inv ≫ i`. Closedness is preserved by
`IsClosedSubgroup.iso_comp`; maximality after each residue-field base change is
preserved by `isMaximalTorus_baseChange_inv_comp_iff`.

Reductivity supplies smoothness and affineness. The published
`localSplitFibrewiseRootDatumExistenceProof` supplies finite reduced full
coordinate root data `P` and `Q` for the two embeddings on every field-valued
fibre. `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise` gives maximality
over the original supplied field `Ω`. The published
`IsFibrewiseRootDatumOf.nonempty_equiv_of_reductive_fieldIso` then compares
`P` and `Q` using the given group isomorphism over `Ω`, retaining the entire
character and cocharacter lattices. It does not require that isomorphism to
preserve the chosen tori. The local Isomorphism Theorem applied to these data
concludes `Nonempty (G ≅ H)`. The resulting isomorphism over `R` is not asserted
to induce the supplied isomorphism over `Ω`.

This is an internal composition of published results and the stated
Isomorphism Theorem. Its mathematical provenance is the derivation in the
unchanged target Markdown: Brian Conrad, *Reductive group schemes* (2014),
registered as `conrad-2014-reductive-group-schemes`, Definition 5.1.1 and
Proposition 5.1.6 for the root datum, Theorem 3.2.6 for maximal-torus conjugacy
inside the field comparison, and Theorem 6.1.17 for the final isomorphism.
Coordinate replacement also follows the published implementation in
`StrictHenselianGenericIsoProof`; this proof starts with the torus witnesses
already supplied by its target, so it has no Henselian hypothesis.

Algebraic closedness of `Ω` is retained in the exact target but is not needed by
the published field-comparison lemma. No reducedness, noetherian, or
characteristic assumption on `R` is introduced.
