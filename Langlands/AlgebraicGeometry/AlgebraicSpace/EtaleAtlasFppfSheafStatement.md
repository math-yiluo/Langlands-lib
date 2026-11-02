# Fppf descent from an etale scheme atlas

Worker 421 formulated this target for the Picard comparison route discussed
with Worker 509. Worker 595 audited the quotient dependencies.

`Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleAtlasFppfSheafStatement`
states the sheaf-condition conclusion of the Stacks Project,
[Lemma 80.12.1, Section 80.12, Tag 076L](https://stacks.math.columbia.edu/tag/076L).
The registered source is
`stacks-smooth-quotient-local-finite-type-2026-11-01`, retained file
`076L.html` with text reading aid `076L.txt`. The entire lemma, proof and
page comments were read. The retained page reports no comments, and no
source-specific errata note was present in the checked workspace or current
Library.

For every actual base scheme `S : Scheme.{u}` and presheaf
`F : (Over S)ᵒᵖ ⥤ Type (u + 1)`, the premises are:

- `F` is a sheaf for `Scheme.etaleTopology.over S`.
- `F` has the scheme-representable diagonal of `AlgebraicSpace.Basic`.
- There are an actual scheme `U : Over S` and a natural transformation
  `a : (schemeYoneda S).obj U ⟶ F` satisfying the published `IsEtale a`
  and `IsSurjective a` predicates.

The conclusion is `Presheaf.IsSheaf (fppfTopology S) F`, where
`fppfTopology S` is exactly `Scheme.fppfTopology.over S`.

These geometric predicates concern represented pullbacks over every scheme,
independently of a topology. In particular, `IsSurjective a` concerns
surjectivity of the underlying scheme projections; it does not assert
objectwise surjectivity of `a`. The etaleness predicate includes
representability of the atlas. The diagonal premise is retained exactly as
in the source.

This formulation uses the existing Library's lifted functor of points and
value universe. The schemes and all test objects remain in `Scheme.{u}`;
only the values lie in `Type (u + 1)`. Every test scheme and every section
is included, with no affine, reduced, quasi-compact, or global-representative
restriction. No hypothesis of finite type, properness, separation,
quasi-separatedness, noetherianity, or field base is imposed.

The source concludes that `F` is an algebraic space in its fppf convention.
Here only its missing sheaf condition is stated, because the other two
conditions are already premises in the published Library interfaces. The
source's proof uses the fppf quotient theorem for an etale equivalence
relation, Theorem 65.10.5. That dependency is not proved by this module.

This contribution is a proposition definition, without a proof. A later
exact-target proof must establish it before it supplies fppf descent for
the actual etale Picard class sheaf. This module imports no Picard statement
and assumes no Picard representability result.
