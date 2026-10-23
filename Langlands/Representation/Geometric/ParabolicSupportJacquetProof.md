# Natural Jacquet comparison for support quotients

The theorem `Langlands.Geometric.padicParabolicSupportJacquetComparison` proves
exactly the published proposition
`Langlands.Geometric.PadicParabolicSupportJacquetComparison.{uF, uV}`.
It compares the successive quotients of the fixed normalized Jacquet image
filtration with normalized radical coinvariants of the corresponding original
support quotients. The comparison is a natural isomorphism on the full smooth
representation category of the source Levi. The field and representation
universes remain independent.

## Implemented proof

For a parabolic-stable subrepresentation `S` of an ambient `GL_n`
representation, `supportInclusion` restricts the ordinary subtype inclusion.
`supportCoinvariantsMap` applies radical coinvariants to this inclusion.
`supportCoinvariantsImageHom` restricts its codomain to the actual image under
`jacquetMk`; on a support vector it sends its coinvariant class to the same
ambient class. Checking this formula on representatives proves Levi
equivariance, with the inverse positive half modulus on both sides.
Surjectivity follows directly from membership in that image.

For an actual finite p-adic extension and smooth ambient representation,
`supportCoinvariantsImageHom_injective` applies the published generic theorem
`coinvariants_map_injective_of_smooth` to the restricted inclusion. Its
hypotheses follow from `Parabolic.unipotentFiniteContainment` and
`Parabolic.isSmooth_radical`. This produces `supportCoinvariantsImageIso`.
The support subrepresentation is only assumed stable under the parabolic;
no extension of its action to `GL_n` is needed.

For subfunctors of normalized parabolic induction restricted to the target
parabolic, the same construction is natural on quotient representatives.
This gives `supportImageNatIso`. For lower and upper subfunctors `S` and `U`,
`supportImageToQuotient` composes the inverse of this natural isomorphism for
`U` with normalized coinvariants of the actual quotient projection from `U`
to its quotient by the pulled-back lower subfunctor.

When `S` is contained in `U`, `supportImageToQuotient_ker` identifies the kernel
with the lower ambient Jacquet image pulled back to the upper image. In one
direction the proof uses the generic algebraic right-exactness theorem
`coinvariants_map_range_eq_ker` for the inclusion of `S.lowerInUpper U A` and
the quotient projection. A representative of the resulting range element
lies in `S` and gives the required ambient image. In the reverse direction,
a representative from `S` has zero quotient projection. Surjectivity of the
map is proved by lifting a radical-coinvariant representative and then a
representative of the original support quotient.

`supportImageQuotientHom` descends this natural map through the actual quotient
of the two ambient images using `Submodule.liftQ`. Equivariance and naturality
are checked after the surjective quotient projection. The kernel equality
proves injectivity of the descended map, and the preceding surjectivity
proof supplies surjectivity. `supportImageQuotientIso` packages these
componentwise bijections as a natural isomorphism.

Finally, `padicParabolicSupportJacquetComparison` specializes this construction
to consecutive steps of `parabolicInductionSupportFiltration`, using
`step_le_next`. The source is definitionally the graded piece of the fixed
`parabolicJacquetSupportFiltration`; the target is precisely the normalized
coinvariants of the original graded support quotient. The proof requires no
positive-rank, admissibility, finite-dimensionality, finite-length, minimality,
or intersection-refinement assumption.

## Provenance and scope

This is the exactness step isolated by the published statement. Its source
correspondence is Bernstein–Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), sections 5.3–5.4, printed page 461: localization embeds
support subspaces into the ambient localized representation and identifies
successive quotients. The registered original is
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The implemented proof uses the Library's concrete radical coinvariants,
finite-containment exactness, and quotient maps.

This module establishes the support-image quotient comparison. The local orbit
comparison, compact-to-smooth induction comparison, and assembly of
`PadicParabolicSupportGradedTheorem` are separate results. All imported
statements and their Markdown pairs are preserved.
