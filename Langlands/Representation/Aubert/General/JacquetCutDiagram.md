# Actual Jacquet diagram of the general standard complex

Worker 691 derived this internal construction from the published general complex,
normalized Jacquet functor, and finite-product coinvariant equivalence. It supplies
the actual homogeneous Jacquet diagram needed to assemble the corrected support
filtration. Its namespace is `Langlands.Aubert.General.JacquetComplex`.

## Objects and maps

The parameters are the standard families `P M U` on finite subsets of a finite
linearly ordered type `ι`, semidirect decompositions `h`, closedness `hclosed`,
unimodular-modulus data `hδ`, monotonicity of `P`, and antitonicity of `U`.
The input `A` is any smooth complex representation; its carrier universe is
`max uG uV`. All three universe parameters `uI`, `uG`, and `uV` are independent.
The constructions also apply when the simple-root type is empty.

`diagram` abbreviates `General.Complex.diagram` after the complement reindexing
of `General.StandardComplex`. In particular, coordinate `s` means the standard
subset `univ \ s`. No transition or sign is changed.

`jacquetDiagram ... A I` has coordinate
`(jacquetFunctor (h I) (hclosed I)).obj (CorrectedFiltration.term ... A s)`.
Its transition is the actual functor image of
`CorrectedFiltration.transition ... A hst`. The identity and composition laws
are proved on representatives using `Jacquet.Localization.mk_surjective` and
the identity and composition laws of the published complex. The formula
`jacquetDiagram_map_mk` records that it sends `[v]` to `[transition v]`.

`totalQuotient` and `degreeQuotient` are the coordinate quotient maps. Their
application formulas are definitional. They commute with extension by zero
(`totalQuotient_extend`), restriction (`degreeQuotient_restrict`), and every
signed insertion (`totalQuotient_step`). The last calculation uses linearity of
the quotient and the unchanged exterior sign. Summing the insertions proves
`totalQuotient_differential`; composing extension, total differential, and
restriction proves `degreeQuotient_differential`.

## Homogeneous comparison

`jacquetDegreeEquiv` is a linear equivalence from the actual normalized Jacquet
module of `StandardComplex.degreeObject` to the homogeneous product of the
Jacquet diagram. Its construction composes:

1. `Jacquet.Localization.trivialEquiv`, identifying localization at the trivial
   character with ordinary coinvariants;
2. `Aubert.FiniteProduct.coinvariantsEquiv`, commuting the actual quotient with
   this finite product;
3. the inverse trivial-character equivalence in every coordinate.

`jacquetDegreeEquiv_mk` identifies its value on a representative with the actual
coordinate quotient. The finite-product theorem supplies both inverse laws; no
choice of splittings of the input representation is used.

`jacquetDegreeRepresentation` is the coordinatewise actual normalized action of
`M I`. The lemma `jacquetDegreeEquiv_intertwining` proves that the comparison
respects this action. On a representative, both actions multiply by the same
inverse half Haar modulus and apply the original action coordinatewise. The
proof uses the comparison's scalar linearity and its formula on representatives.

`degreeMorphism` is the published signed differential as a smooth morphism,
with the same complement reindexing. The theorem
`jacquetDegreeEquiv_differential` compares its actual normalized Jacquet image
with the signed differential of `jacquetDiagram`. Surjectivity of the quotient
reduces the assertion to `degreeQuotient_differential`. This proves compatibility
of the actual maps, in addition to equivalence of their source and target modules.

## Provenance and scope

This is derived infrastructure, with no additional claim taken from the
literature. The declaration-level dependencies are Worker 194's published
`General.Complex.diagram`, `degreeObject`, and `degreeMorphism`, and
`General.StandardComplex.removedFamily`; Worker 379's published
`General.CorrectedFiltration.term` and `transition`; and the published
`Jacquet.Localization.trivialEquiv`, `mk_surjective`, and
`Aubert.FiniteProduct.coinvariantsEquiv`. Those imported files and their existing
authorship are preserved. The signed calculation follows the existing
`Aubert.ActualCutComplex` Jacquet-diagram construction, now using the general
normalized functors and actual subgroup families. It uses no GL-specific Jacquet
equivalence or general-to-GL identification.

The unit has no finite-length, irreducibility, or admissibility premise on `A`.
It does not prove graded exactness, produce Bruhat or Coxeter data, or prove
`RationalCorrectedTheorem36Statement`. Those remain separate obligations. No
Langlands-classification, character-independence, geometric-lemma, or adjointness
theorem is applied in this unit's proof bodies. Its representation-theoretic
inputs are the imported construction and quotient APIs just named.
