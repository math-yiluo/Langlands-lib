# Proof: multiplicative-type subgroups of a fibre lift to an étale neighbourhood

Module `Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleLiftProof`, namespace
`Langlands.GroupScheme`.

## Result

`multiplicativeTypeEtaleLift : MultiplicativeTypeEtaleLiftStatement.{u}` proves the published
statement `Langlands.GroupScheme.MultiplicativeTypeEtaleLiftStatement` (Conrad, *Reductive
group schemes* (2014), Proposition 3.1.6, with the remark after it; SGA 3, Exp. XI, 5.8(a)) in
every universe, with no extra hypotheses. Let `G → S` be a smooth affine group scheme, `s ∈ S`,
and `i₀ : H₀ → G_s` a closed subgroup of multiplicative type of the fibre over `κ(s)`. Then
there are:

- an étale map `p : U → S` with a point `b : Spec κ(s) → U` over `s`;
- a group `H` of multiplicative type over `U` with a closed immersion `i : H → G_U`;
- an isomorphism of the fibre of `H` at `b` with `H₀`, under which the fibre of `i` at `b`
  is `i₀`.

The module also proves `MultiplicativeTypeSubgroupModuli.finiteTypeChartCover :
MultiplicativeTypeSubgroupModuli.FiniteTypeChartCoverStatement.{u}`. For every finitely
generated commutative ring `R` and smooth affine group `G` over `Spec R`, some family of
open charts of the functor of closed multiplicative-type subgroups of `G` covers all field
points.

## The Lean proof

The proof follows SGA 3, Exp. XI: a chart of the functor of closed multiplicative-type
subgroups, through a point carrying `i₀`, is smooth, so it has étale-local sections. It
avoids the Artin approximation used in Conrad's proof. It constructs no global moduli
scheme: one chart through the given point is enough.

1. `finiteTypeChartCover` is
   `HomScheme.MultiplicativeTypeChart.finiteTypeChartCover_of` (module
   `HomScheme.MultiplicativeTypeChartCover`) applied to three inputs:
   - the fppf splitting hypothesis `FppfSplitStatement`, discharged by
     `HomScheme.exists_fppf_diagPoints` (module `HomScheme.MultiplicativeTypeSubgroupSplitting`).
     Over an affine test, a closed multiplicative-type subgroup is, on finitely many affine
     flat, locally finitely presented pieces covering the test, the range of a closed
     homomorphism from a diagonalizable group `D(Λ)` with `Λ` finitely generated;
   - smoothness of coordinate Hopf algebras of smooth affine groups, the Library's
     `HomScheme.FiniteDiagonalizable.smooth_hopfAlgebra`;
   - smoothness of the algebras `W R A L` representing Hopf points of `D(L)` for finite
     `L`. This is the Library instance `FiniteBialgebraHom.smooth_homAlgebra`, found by
     `inferInstance` because `MixedChartAlgebra.W R A L` unfolds to
     `HomAlgebra R A (AddMonoidAlgebra R L)`.
2. `finiteTypeChartCover_of` uses the window charts on lattices `ℤ^c × F`. They are built in
   `HomScheme.MultiplicativeTypeChartConstruction` from the ring-level data of
   `Algebra.MixedChartRing` / `Algebra.MixedChartExistence`. They are open charts by
   `HomScheme.MultiplicativeTypeChartInjective` and `HomScheme.MultiplicativeTypeChartOpen`
   together with the affine-test criterion
   `MultiplicativeTypeSubgroupModuli.isOpenChartOfAffines`. They cover the field points by
   `MultiplicativeTypeChartCover.coversFieldPoints`.
3. `multiplicativeTypeEtaleLift` is
   `MultiplicativeTypeSubgroupModuli.multiplicativeTypeEtaleLift_of_finiteTypeCharts`
   (module `HomScheme.MultiplicativeTypeSubgroupChartCoverReduction`) applied to
   `finiteTypeChartCover`. That theorem does two things:
   - It extends chart covers from finite-type affine bases to all bases (`chartCoverReduction`:
     finite-type models of affine bases, base change and transport of charts, and charts
     over the members of an affine open cover of `S` combined by `hasChartCover_of_openCover`).
   - It applies `multiplicativeTypeEtaleLift_of_chartCover` (module
     `Torus.MultiplicativeTypeChartLifting`). The field-point cover gives a chart `M` and a
     `κ(s)`-point `x` of `M` evaluating to `i₀`. `M` is smooth over `S`, so the published
     `Langlands.AlgebraicGeometry.exists_pointed_etale_section` extends `x` to a section over
     a residually trivial étale neighbourhood `U` of `s`. The chart family pulled back along
     this section is the required `i : H → G_U`. `recover_subgroup_fibre_inclusion`
     identifies its fibre at `b` with `i₀`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
