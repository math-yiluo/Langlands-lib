# Actual radical convergence: proof of `RationalSchwartzConstantTermConvergenceStatement`

Module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSchwartzConstantTermConvergenceProof`,
namespace `Langlands.HarishChandraSchwartz`.

## Result

`Langlands.HarishChandraSchwartz.rationalSchwartzConstantTermConvergence :
RationalSchwartzConstantTermConvergenceStatement.{u}`

The statement and its correspondence with Waldspurger 2003 (III.6, the Schwartz space `C(G)` and
its constant terms; II.4.5, the estimate behind their convergence) are in
`RationalCuspidalConvergenceStatements.md`. It says: for a nonarchimedean local field `F`
(of either characteristic), a connected reductive `G` over `F` with maximal split torus `i` and
generic cocharacter `ν`, a compact open subgroup `K` of `G(F)` with `G(F) = P₀(F) K`, a closed
matrix representation `ρ` defining the height `σ`, every `f` in the actual Schwartz space
`RationalSchwartzSpace hKc hPK ρ`, every finite set `I` of simple roots whose root set
`J = rootSet i ν I` is a proper subset of the simple relative roots, every Haar measure `ν_U` on
the actual unipotent radical `U_J(F)` (`standardUnipotentPoints i ν J`) and all `x, y ∈ G(F)`,
the function `v ↦ f(x v y)` is integrable on `U_J(F)` for `ν_U`.

The theorem is proved at an arbitrary universe `u` and has no hypotheses. Its inputs are
published Library results imported by name. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The Lean term is one application:

```
rationalConstantTermEstimate.schwartzConstantTermConvergence
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

It combines three published results.

1. `rationalConstantTermEstimate : RationalConstantTermEstimateStatement.{u}` (module
   `RationalConstantTermEstimateProof`) proves Waldspurger's Proposition II.4.5 on actual rational
   points: for a compact open `K0` carrying the structural premises
   `SimultaneousStandardBasisAt i ν K0`, `FiniteCartanCovering F i ν K0` and
   `StandardLeviCartanCovering F i ν J K0`, the normalized constant-term integral of `Ξ` against a
   negative power of `1 + σ` is bounded by `Ξ^{M_J}` times any prescribed negative power of
   `1 + σ` on `M_J(F)` (`ConstantTermEstimate`).
2. `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence :
   JointSpecialCompactBasisExistenceStatement.{u}` (module
   `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves the existence of a special compact
   subgroup with its simultaneous standard basis, standard-Levi inheritance, Iwasawa products and
   Cartan comparisons (Renard V.5.1–V.5.2), for every connected reductive group over every
   nonarchimedean local field, maximal split torus and generic cocharacter.
3. `RationalConstantTermEstimateStatement.schwartzConstantTermConvergence` (module
   `RationalConstantTermConvergenceReduction`) is the reduction: from the two propositions above
   it derives `RationalSchwartzConstantTermConvergenceStatement`. Given the data of the target, it
   uses `exists_constantTermPremises_of_joint` (module `RationalSpecialCompactConstantTermPremises`)
   to obtain from item 2 one compact open `K0` with `G(F) = P₀(F) K0`, the three structural
   premises of item 1 and the Levi factorization `M_J(F) = (P₀(F) ∩ M_J(F))(K0 ∩ M_J(F))`. It then
   applies `RationalConstantTermEstimateStatement.integrable_mul_mul` (module
   `RationalCuspidalConvergenceReductions`) with this `K0` and the given `K`, which compares the
   Schwartz spaces for `Ξ_K` and `Ξ_{K0}` and applies the estimate of item 1 to the two-sided
   translate of `f`. The description of this reduction is in
   `RationalConstantTermConvergenceReduction.md`.

The compact open subgroup `K0` is produced inside the proof; the theorem keeps the given `K`, `ρ`
and Haar measure, and adds no `ConstantTermEstimate`, Cartan covering, height estimate or
convergence premise. When the relative rank is zero there is no proper root subset and the
quantifier over `I` is empty; the proof does not treat this case separately.

## Dependencies

All three imported modules, `RationalConstantTermConvergenceReduction`,
`RationalConstantTermEstimateProof` and `Langlands.BruhatTits.SpecialCompact.JointBasisProof`, are
in the Library. Applying the published implication
`RationalSchwartzConstantTermConvergenceStatement.vanishingComparison` (module
`RationalCuspidalConvergenceStatements`) to this theorem gives
`RationalCuspidalVanishingComparisonStatement`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`):
Proposition II.4.5, printed pp. 262–263, and III.6, printed pp. 271–272. The Lean proof follows
the route of the reduction above, through Proposition II.4.5 for the actual Harish-Chandra
function and the special compact subgroup of Renard V.5.1–V.5.2.
