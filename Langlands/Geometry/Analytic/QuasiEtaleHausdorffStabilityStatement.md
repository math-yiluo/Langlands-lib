# Statement: stability of quasi-étale morphisms under Hausdorff hypotheses

This module states, without proof, four propositions in the namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. Three of them are the
stability properties of Berkovich 1994, Lemma 3.1, for arrows whose relevant
objects have Hausdorff underlying spaces. The fourth says that these three
give the fibre products of the equivariant quasi-étale sites.

Throughout, `K : Type u` is a complete ultrametric normed field, all objects
lie in the localized category `LocalizedCategory.{u, v, v} (K := K)`, and
`quasiEtale` is the Library predicate of the module `QuasiEtaleSite`. "The
underlying space of `Y` is Hausdorff" means
`T2Space (localizedSpaceFunctor.obj Y)`. Each Hausdorff condition is an
explicit hypothesis of the proposition. The universes are those of
`QuasiEtaleStabilityStatement`: `u` for the field and `v` for the spaces and
atlas indices.

## The statements

1. `QuasiEtaleHausdorffCompStatement K`. Let `f : A ⟶ B` and `g : B ⟶ C` be
   quasi-étale, and suppose the underlying spaces of `A` and `B` are
   Hausdorff. Then `f ≫ g` is quasi-étale. No hypothesis is made on `C`.
2. `QuasiEtaleHausdorffBaseChangeStatement K`. Take a square
   `IsPullback f' g' g f` with `f' : Y' ⟶ Y`, `g' : Y' ⟶ X`, `g : Y ⟶ S` and
   `f : X ⟶ S`. Suppose `g` is quasi-étale and the underlying space of `Y` is
   Hausdorff. Then the parallel projection `g'` is quasi-étale. As in
   `QuasiEtaleBaseChangeStatement`, `IsPullback` is the categorical pullback
   property in the localized category. The statement covers every pullback
   square and does not assert that pullbacks exist. No hypothesis is made on
   `X`, `S` or `Y'`.
3. `QuasiEtaleHausdorffOverMorphismStatement K`. Let `f : Z ⟶ Y` and
   `g : Y ⟶ X`. Suppose `g` and `f ≫ g` are quasi-étale and the underlying
   space of `Y` is Hausdorff. Then `f` is quasi-étale. Only the middle object
   `Y` is assumed Hausdorff; no hypothesis is made on `Z` or `X`.
4. `EquivariantQuasiEtalePullbacksHausdorffReductionStatement` (universes
   `u`, `v` and `z`) is the implication: if statements 1, 2 and 3 hold for
   every complete ultrametric normed field `K : Type u`, then
   `EquivariantQuasiEtalePullbacksStatement.{u, v, z}` holds (module
   `EquivariantSitePullbacksStatement`: the categories `Qét(X(G))` have fibre
   products computed on underlying analytic spaces with the diagonal action).
   Its premises are the three stability statements and nothing else.

Statements 1–3 are the statements `QuasiEtaleCompStatement`,
`QuasiEtaleBaseChangeStatement` and `QuasiEtaleOverMorphismStatement` of the
module `QuasiEtaleStabilityStatement`, restricted by the Hausdorff hypotheses
above. Those three are stated there for all objects and are not changed by
this module.

## Original source

Berkovich, *Vanishing cycles for formal schemes*, Invent. Math. 115 (1994),
registered as `berkovich-1994-vanishing-cycles-formal-schemes`, §3. The
definition of quasi-étale morphisms is on printed p.543 (PDF p.5), and
Lemma 3.1 is on printed p.544 (PDF p.6):

> (i) Quasi-étale morphisms are preserved under compositions, under any base
> change functor and under any ground field extension functor.
> (ii) If Y and Z are quasi-étale over X, then any X-morphism Z → Y is
> quasi-étale.

Statement 1 is the composition clause of (i), statement 2 its base change
clause and statement 3 is (ii), each for the Hausdorff objects named above.
The ground field extension clause is not stated, as in
`QuasiEtaleStabilityStatement`.

## Provenance of the Hausdorff hypotheses

The statements are derived. Berkovich makes no Hausdorff hypothesis, and his
proof of Lemma 3.1 is one sentence: "All the statements easily follow from
the corresponding properties of étale morphisms and Theorem 3.4.1 from
[Ber2]", where [Ber2] is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces*, Publ. Math. IHÉS 78 (1993), registered as
`berkovich-1993-etale-cohomology`, Theorem 3.4.1 (printed p.65, PDF p.62).

The Hausdorff hypotheses are those under which the charts of the quasi-étale
condition can be taken through the point. Berkovich's definition (p.543) asks at each point `y` for
affinoid domains `V₁, …, Vₙ` whose union is a neighbourhood of `y`. It does
not ask that `y ∈ Vᵢ`, and the Library's `IsQuasiEtaleAt` follows it. When
the source is Hausdorff, the affinoid domains are compact, hence closed, and
the domains missing `y` can be dropped:
`hasLocalDomainEtaleFactorizations_of_quasiEtale` (module
`QuasiEtaleDomainLocality`) gives, for a quasi-étale arrow with Hausdorff
source, finitely many analytic domains through each point whose union is a
neighbourhood and on which the arrow factors through an étale space.

Without a Hausdorff hypothesis, a compact domain missing `y` can accumulate at
`y`. Glue two closed discs of radius two along the complement of the closed
unit disc, and let `y` be the Gauss point of radius one in the first copy.
The unit disc of the first copy and the whole second copy cover the glued
space, the second copy misses `y`, and the unit disc is not a neighbourhood of
`y`. The Markdown of the modules `QuasiEtaleCompactRefinementsObstruction`
(this example) and `QuasiEtaleLocalDomainFactorizationsStatement` (two unit
discs glued along the open unit disc) describes such doubled discs. The
pointed condition for an arbitrary source is the proposition
`QuasiEtaleLocalDomainFactorizationsStatement`. Its counterpart in Berkovich
geometry follows from Ducros, *Families of Berkovich spaces*, Astérisque 400
(2018), registered as `ducros-2018-families-berkovich-spaces`, which recalls
Berkovich's definition in 5.4.10 and proves in Lemma 5.4.11 (printed pp.120–121 of
arXiv:1107.4259v6) that it is equivalent at each point to his own notion of
quasi-étaleness. His notion is local at a point for the analytic domains
containing it (5.2.10), and the proof of the converse direction produces
affinoid domains through the point, using his Theorem 5.4.6 and Berkovich
1993, Theorem 3.4.1. The statements of this module avoid that theory: under
their Hausdorff hypotheses the charts through the point are given by
`hasLocalDomainEtaleFactorizations_of_quasiEtale`.

The hypotheses of statements 1–3 are also the ones available where the
statements are applied. In statement 4, every object of `Qét(X(G))` is a
`G`-space, and the property `gSpaceProperty` defining `GSpace` (module
`ContinuousAnalyticAction`) includes that its underlying space is Hausdorff.
For a cospan `U₁ → U₃ ← U₂` in `Qét(X(G))`, statement 3 is applied with
middle object `U₃`, statement 2 to `U₁ → U₃` with source `U₁`, and
statement 1 to `P → U₂ → X`, where `P` is the pullback vertex.
`hasCompactPairPreimages_of_quasiEtale` (module
`LocalizedPullbackCompactPreimages`) gives that `P` is Hausdorff when `U₁`
and `U₂` are. Statement 4 is derived from the Library's
`equivariantQuasiEtalePullbacks_of_stability` (module
`EquivariantSitePullbacksReduction`), which has the same conclusion from the
general statements of `QuasiEtaleStabilityStatement`.

## Scope

This is a statement module: nothing is proved here.
