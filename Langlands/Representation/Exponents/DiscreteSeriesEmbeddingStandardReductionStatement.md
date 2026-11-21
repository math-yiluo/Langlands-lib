# Standard parabolic witnesses for discrete-series embeddings

`Langlands.Aubert.General.RepresentedParabolic.DiscreteSeriesEmbeddingStandardReductionStatement`
compares two existence conditions on an irreducible smooth complex
representation `π` of the rational points of a connected reductive group `G`
over a Hausdorff nonarchimedean local field `k`. It uses the canonical topology
on `G(k)` with local compactness and the nonarchimedean group structure. The
field has a universe parameter independent of the common universe of the
representation carriers.

On the left, the witness has a rational parabolic `p : P ⟶ G`, a rational Levi
`l : M ⟶ P`, and a geometric unipotent radical `r : U ⟶ P` with the Levi-radical
multiplication isomorphism. It has an irreducible smooth representation `σ` of
`M(k)` that is square-integrable modulo the center for every Borel measurable
structure and Haar measure on `M(k) ⧸ Z(M(k))`. The embedding is an injective
intertwiner from `π` into the normalized induction of `σ` given by
`leviInductionFunctor`. This is the witness in
`TemperedIrreducibleDiscreteSeriesStatement`.

On the right, a maximal split torus `i : T.toGrp ⟶ G` and a generic cocharacter
`ν` determine a fixed standard family. The witness also specifies a subset `J`
of the simple relative roots. The subgroup functor ranges of `p` and `l ≫ p`
are `standardParabolic i ν J` and `standardLevi i ν J`, respectively. The range
equalities express standardness for both maps at the same index. The whole
group may be the parabolic, as in Renard's existence proof.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VII.2.6 Theorem, printed p. 231 (PDF p. 237), uses a standard
parabolic for its discrete-series embedding. V.3.8–9, printed pp. 111–112 (PDF
pp. 117–118), fixes the standard family and gives rational conjugacy of
parabolics into that family. V.3.1, printed p. 110 (PDF p. 116), gives conjugacy
of Levi factors within a parabolic. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This derived statement makes explicit the comparison between the witness
condition in the Library and Renard's standard witness. The standard witness
supplies a rational one by dropping its range constraints. In the other
direction, a single rational conjugating point standardizes both ranges.
Keeping the same Levi source identifies its inducing representation and the
square-integrability condition on its center quotient. Transport of the
normalized induction embedding supplies the standard witness. The equivalence
is formulated independently of temperedness.
