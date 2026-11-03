# Actual Cartan families and conditional finite torus generation

Worker 1342.

`Langlands.GroupScheme.CartanSubgroup G` bundles an actual group scheme
`C.group`, homomorphism `C.inclusion : C.group ⟶ G`, and proof
`C.isCartan : IsCartanSubgroup C.inclusion`. It indexes every presentation
of every Cartan subgroup over `k`. No quotient by isomorphism is taken,
and the type contains no assertion of existence, smoothness, or generation.
Its field `k : Type u` is arbitrary; its presentation type may live in a
higher universe. This is an internal derived family interface for the
published Cartan predicate of `Cartan.Basic`.

`reductiveFiniteTorusGeneration_of_cartanGeneration` proves the implication

`CartanGenerationStatement.{u} → MaximalTorusCentralizerStatement.{u} →
ReductiveFiniteTorusGenerationStatement.{u}`.

Both structural propositions remain explicit premises. The result applies
to every infinite field and every connected reductive group in the target,
with arbitrary characteristic, imperfect fields, nonsplit groups and rank
zero retained. It is a conditional intermediate API lemma and is not an
unconditional proof of finite torus generation or rational-point density.

The proof uses `CartanSubgroup G` as the index type for the family of all
Cartan embeddings in `G`. The centralizer-statement premise, through the
published lemma `IsCartanSubgroup.isTorus_of_centralizerStatement`, makes
each source a torus. `Torus.Geometry` gives smoothness and connectedness.
A Cartan inclusion is closed, and its composite with the affine structure
map of `G` is the structure map of its source, which proves affineness.

The Cartan-generation premise says that any closed competitor containing
this entire family has top all-test range. The generic theorem
`FiniteGeneration.exists_finite_generating_subfamily_of_pointedImageGeneration`
then chooses a finite subfamily generating `G`. Its pointed-image premise
is discharged by the published unconditional theorem
`ImageGeneration.pointedImageGeneration`; no such premise remains in this
module's implication. That generic argument includes the empty family and
uses the maximal Lie dimension of its smooth connected generated
representatives. Reindexing the resulting finite subtype with
`Fintype.equivFin` yields the required natural number and `Fin m` family.
The selected embeddings retain their original closedness and torus proofs,
and a competitor containing the reindexed family contains the original
finite subfamily, so its range is top on every test scheme.

## Provenance and remaining obligations

The bundled family and conditional adapter are derived internal content.
They implement the composition behind the source derivation of finite
subfamilies recorded in `Reductive/TorusGenerationStatement.md`. The
mathematical source is Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:
Theorem 17.91, printed p.381/PDF p.397 (Cartan generation), and Corollary
17.84, printed p.379/PDF p.395 (maximal tori are self-centralizing in
connected reductive groups). These are motivation for the two retained
premises, not propositions proved by this module. The proof of the finite
selection step is the published generic dimension argument, not a new
formalization of Milne's structural results.

The complete registered errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02`, SHA256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`,
was read and has no correction to 17.84 or 17.91. This module establishes
neither retained structural premise. A proof of each premise, with all its
own hypotheses discharged, is still necessary to derive the unconditional
finite-torus-generation and host density targets.
