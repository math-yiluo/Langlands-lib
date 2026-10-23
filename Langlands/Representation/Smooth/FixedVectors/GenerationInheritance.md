# Inheritance of semisimple fixed-vector generation

This module proves the published proposition
`Langlands.SemisimpleFixedVectorsGenerationInheritanceStatement`.
The closing theorem `Langlands.semisimpleFixedVectorsGenerationInheritance`
assembles all three clauses with independent coefficient, group, source-carrier
and target-carrier universes.

Worker 196 authored the complete three-lemma proof and mathematical interface
in the parent development. Worker 213 added the closing theorem against the
published statement and prepared this account of the proof. The result is an
internal algebraic derivation from semisimple group-algebra modules, equivariant
maps, and the existing actual smooth-subquotient presentation; it is not a
translation of a separately cited literature theorem.

For a representation `rho` and subgroup `K`, generation by fixed vectors means
that every invariant subspace containing `fixedVectors rho K` is the whole
representation.

`Langlands.semisimple_fixedVectors_generate_of_surjective` proves that
semisimplicity and generation by `K`-fixed vectors pass through a surjective
intertwiner. Semisimplicity passes to the target through the corresponding
group-algebra module map. For generation, the proof takes the invariant inverse
image of a target subrepresentation containing the target's fixed vectors.
Equivariance maps source fixed vectors into target fixed vectors, so the inverse
image contains the source's fixed vectors. The source generation assumption
makes this inverse image the whole source. Surjectivity then makes the target
subrepresentation the whole target. Surjectivity on fixed vectors is not
assumed or used in this proof.

`Langlands.semisimple_fixedVectors_generate_of_injective` uses the extension
property of the semisimple ambient group-algebra module to extend the identity
on the source across the injection. This gives an equivariant retraction.
The retraction is surjective because it is a left inverse, so the preceding
surjection lemma gives both conclusions for the source.

`Langlands.SmoothRep.semisimple_fixedVectors_generate_subquotient` expresses
an actual smooth subquotient `B` of `A` as a smooth representation `C` with an
injective intertwiner into `A` and a surjective intertwiner onto `B`, using
`SmoothRep.isSubquotient_iff_exists`. It restricts both maps to `H`.
The hypothesis `K ≤ H` lets `Langlands.fixedVectors_comp_subtype` identify the
fixed space for `K.comap H.subtype` in each restriction with the ambient
`K`-fixed space. Applying the injection lemma and then the surjection lemma
gives the two conclusions for `B`. Thus both the ambient fixing subgroup `K`
and the restricted acting subgroup `H` are retained.

The first two lemmas permit independent source and target carrier universes
and require no topology or smoothness. The third uses the same carrier
universe for both smooth representations, as required by the existing
subquotient relation, and only assumes a topology on the acting group.
None of these results assumes normality, openness, compactness, admissibility,
finite dimensionality, finite length, irreducibility, or surjectivity on fixed
vectors. The closing theorem introduces exactly the universally quantified
data of the three published clauses and applies the corresponding lemma.
The module establishes this inheritance bundle; it makes no claim to the
cuspidal constituent theorem.
