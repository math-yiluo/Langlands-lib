# Affineness and closedness of the relation scheme

Authors: Worker 148 (Lean implementation and proof explanation), with Workers 239
and 712 (the direct scheme proof route in the published statement).

The theorem
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationAffineRelation.{u}` proves
exactly the published proposition
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineRelationStatement.{u}`:
for an etale equivalence relation `E` on an affine scheme, a finite surjective
cartesian cover by a relation admitting an affine quotient implies
`IsAffine E.R` and `IsClosedImmersion (prod.lift E.t E.s)`. The universe `u` is
arbitrary, and the theorem adds no hypotheses. The published statement and the
module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` are imported
unchanged. The only additional import is Mathlib's `AlgebraicGeometry.ZariskisMainTheorem`.

## Implemented proof

Write `j = (t, s) : E.R → E.U × E.U`. Unpack the given cover as a relation `E'`,
a finite surjective map `f : E'.U → E.U`, and a map `g : E'.R → E.R`. The
cartesian-hom data supply `g ≫ E.t = E'.t ≫ f` and the pullback square
`IsPullback g E'.s E.s f`. Unpack the affine quotient of `E'` as an affine
scheme `M` and `q : E'.U → M` with `IsPullback E'.t E'.s q q`.

The first private helper, `closedImmersion_pair_of_pullback`, applies to any
such pullback square. It constructs the pullback square whose top map is
`t ≫ q`, left map is `(t, s)`, right map is the diagonal `M → M × M`, and
bottom map is `q × q`. Its universal property is proved directly using the
universal property of the original pullback and the product projections. The
diagonal is a closed immersion because the affine scheme `M` is separated.
Base change therefore shows that `j' = (E'.t, E'.s)` is a closed immersion.

The second private helper, `isFinite_prod_map_self`, proves that `f × f` is
finite. It first obtains finiteness of `f × id_Z` from
`IsPullback.of_prod_fst_with_id`. Product symmetries then give finiteness of
`id × f`. Their composition is `f × f`, so it is finite.

The two projection equations for the cartesian hom give
`g ≫ j = j' ≫ (f × f)`. The right side is universally closed: a closed
immersion is universally closed, a finite map is proper and hence universally
closed, and universal closedness is closed under composition. Base change of
the surjective `f` in the cartesian square makes `g` surjective.
`UniversallyClosed.of_comp_surjective` now gives universal closedness of `j`.

The field `E.mono_lift` makes `j` a monomorphism, so it is separated. The field
`E.etale_t` makes `E.t` locally of finite type. Since `j ≫ prod.fst = E.t`,
`locallyOfFiniteType_of_comp` makes `j` locally of finite type. These properties
assemble into `IsProper j`, and
`IsClosedImmersion.iff_isProper_and_mono` makes `j` a closed immersion.

Finally, `prodIsoPullback` identifies `E.U × E.U` with the fibre product of
two affine schemes over the affine terminal scheme. Mathlib's affine-pullback
instance gives affineness of the product. A closed immersion is an affine
morphism, and `isAffine_of_isAffineHom j` gives affineness of `E.R`.

The argument uses no Noetherian or extra separatedness or quasi-compactness
assumption. Only the affine target and pullback square of the covering quotient
are used; its flatness, local finite presentation and surjectivity are not
needed. The relation's equivalence-relation laws and second etale projection
are likewise not used by this direct proof.

## Provenance

This is the derived scheme argument suggested under “Scope and role” in the
published statement's Markdown. It does not construct or use an algebraic space
quotient. The final closed-immersion criterion is Stacks Project Lemma 41.7.2,
Tag [04XV](https://stacks.math.columbia.edu/tag/04XV), equivalence of conditions
(1) and (2), as implemented in Mathlib. It is also the passage from condition
(6) to condition (1) after deriving separatedness from the monomorphism.

The retained original is `04XV.html` in the registered source
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`.
The complete original page and proof were read, including its empty comments
section; no source-specific errata note was present. The remaining steps use
Mathlib's finite-map, base-change, separatedness and affineness results as
identified above. This companion describes the implemented proof rather than
the algebraic-space provenance of the statement.
