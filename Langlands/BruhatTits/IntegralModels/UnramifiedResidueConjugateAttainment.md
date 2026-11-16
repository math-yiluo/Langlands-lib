# Integral conjugates of actual downstairs facet images

This internal supporting unit proves
`UnramifiedResidueConjugateAttainmentStatement.{u}` with
`unramifiedResidueConjugateAttainment`, at arbitrary universe `u`. At every
point of the supplied downstairs apartment, every residue-field parabolic of
the actual supplied model's reductive quotient is the inverse integral
conjugate of an actual incident facet-model quotient image. The equality is
an equality of subgroup functors on every scheme test.

The final statement retains the complete descended-building hypotheses of
`UnramifiedFacetParabolicOrderStatement`: the seven building/apartment axioms;
the injective equivariant building map and compatible affine apartment map;
the fixed-point, fixed-locus surjectivity, special-point reflection and exact
facet-restriction hypotheses; and fixedness under the bounded torus kernel.
It also retains the supplied zero datum and facet-model family with the
unramified integral-point characterization at every facet. Smoothness is
both part of the model data and explicitly retained as in the host statement.
The quotient is an actual `SpecialFibreQuotientData` satisfying
`IsReductiveQuotient`. The generic torus factorization and integral torus are
constructed inside the proof, without additional premises.

The witnesses are a section `s` of the target neutral model and an incident
facet `Fd`. The asserted image is the schematic image of the actual family
comparison `Mf.morphism`, followed by the supplied quotient projection and
the inverse inner automorphism of the quotient point obtained by reducing
`s` and projecting it. It is exactly the range of the prescribed parabolic
inclusion. The source facet has not been translated to absorb this conjugation;
the theorem therefore supplies attainment up to integral conjugation at
apartment points, not the host order bijection.

The implemented proof has four parts:

1. `SpecialFibreQuotientData.quotientReduction_surjective` works over an
   arbitrary Henselian domain with perfect residue field. The represented
   smooth connected unipotent radical is affine as a closed subgroup of the
   model's affine special fibre, and is split by `perfectFieldUnipotentSplit`.
   The published integral-model quotient lifting theorem then proves
   surjectivity of reduction followed by quotient projection.
2. `FacetModelData.exists_integralConjugate_incidentFacet_quotientImage_eq_parabolic`
   uses rational dynamic classification and smooth maximal split torus
   conjugacy to conjugate a parabolic cocharacter into the actual quotient
   torus. It lifts the conjugating point to an integral section using the
   preceding surjectivity result. Inverse canonical cocharacter
   specialization lifts the quotient-torus cocharacter, and published
   residue cocharacter attainment gives an actual incident facet and the
   exact image of its supplied family comparison.
3. `Dynamic.range_eq_parabolic_comp_iso_iff` compares the parabolic range
   after conjugation. The schematic-image/range and subgroup-comap formulas
   for an isomorphism cancel this conjugation with the inverse inner
   automorphism in the conclusion. This step uses full subgroup functors,
   without replacing the image by its rational points.
4. The final wrapper obtains the generic torus factorization from
   `unramifiedDescendedApartmentTorus`, common apartments from the supplied
   realization's building axiom, and the actual integral torus from
   `exists_integralTorus_at_apartmentPoint`. It then applies the preceding
   conjugate-attainment lemma to that torus and quotient.

The provenance is internal composition of Library classification, rational
conjugacy, perfect-field unipotent splitness, quotient lifting, descended
torus containment and actual residue cocharacter attainment. It makes no
additional original-literature translation claim. Universal image
parabolicity, recovery of facets, and direct attainment without conjugation
remain separate obligations for the full order-bijection theorem.
