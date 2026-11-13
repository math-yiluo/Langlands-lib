# Proof of restriction of an apartment to a standard Levi subgroup

The theorem
`Langlands.Geometry.Building.leviApartmentRestriction` has exactly the type
`Langlands.Geometry.Building.LeviApartmentRestrictionStatement.{u}` at arbitrary
universe `u`. It proves the published formulation of Kaletha–Prasad
Lemma 6.7.1 (1)–(4) for supplied apartment data over a nonarchimedean local
field and the actual standard Levi subgroup at the same maximal split torus.

The source is Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
§6.7 and Lemma 6.7.1, printed p.233 / PDF p.264. The registered
`kaletha-prasad-2024-corrections`, version of 1 November 2024, PDF p.32,
contains no correction to this lemma. The statement module's Markdown
explains the local-field and standard-Levi scope, the split-torus compatibility
encoded in `KPApartmentData`, and the expression of part (4) through
surjectivity and the common kernel of the Levi roots. Part (5) is outside this
target.

The implemented proof first uses
`StandardLeviSplitComponent.exists_standardLevi_eq_dynamicCentralizer` from
`Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof` to express
the standard Levi as the dynamic centralizer of one cocharacter of the
unchanged torus. The same module's proved
`standardLeviSplitComponentStatement` supplies smoothness of the actual Levi
representative. The remaining structural inputs are
`Standard.isRepresentedBy_leviHom`, `Standard.isClosedSubgroup_leviHom`
from `Langlands.GroupScheme.Rational.StandardRepresentability`, and
`Standard.leviTorusHom_comp`,
`Standard.isMaximalSplitTorus_leviTorusHom` from
`Langlands.Geometry.Building.SpecialCompactLevi`; the ambient smoothness,
affineness, connectedness and split-torus properties come from the given
connected reductivity and maximal split torus.

It then takes `DM` to be `leviRestrictedApartmentData` from
`Langlands.BruhatTits.SpecialCompact.LeviApartmentRestriction`. This is the
image of the original valuation class under restriction, normalized to
infinity on characters outside the Levi roots. The published construction
already proves its valuation axioms, split-torus compatibility and normalizer
stability. Its `leviApartmentProjection` and
`isLeviRestriction_leviApartmentProjection` give a restriction for every
ambient point. Its `leviApartmentProjection_surjective` gives every Levi
point as a restriction. These establish the first two conclusion clauses.

Two internal derived lemmas in this module establish the fibre clause:

- `leviRestriction_val_eq_vadd` says that any two restriction pairs carry
  a translation of ambient valuations to the same translation of Levi
  valuations. On a Levi root it follows from the defining equality
  `IsLeviRestriction` and `RootFunctionFamily.vadd_apply`; off those roots
  both Levi valuations are infinity by
  `IsRootDatumValuation.eq_top_of_not_mem_roots`.
- `leviRestriction_eq_iff_exists_vadd` first obtains an ambient translation
  from `KPApartmentData.equipollent_of_mem`. The preceding lemma makes it a
  translation between the restricted valuations. By the published
  `IsRootDatumValuation.vadd_eq_self_iff` and `mem_rootAnnihilator` in
  `Langlands.Geometry.Building.KPApartment`, it fixes the restricted
  valuation exactly when every Levi root vanishes on its vector.
  `KPApartmentData.Apartment.ext` converts valuation equality to point
  equality. This replaces the source's dimension count with the already
  proved valuation stabilizer criterion, whose finite-value input is axiom V 0.

The proof adds no hypothesis and assumes no unproved proposition target.
It uses the supplied `D` without constructing a building, assuming
availability, or requiring full-centralizer omega compatibility.
