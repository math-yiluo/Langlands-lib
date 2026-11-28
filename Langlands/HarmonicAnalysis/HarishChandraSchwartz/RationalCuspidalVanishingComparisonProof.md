# The vanishing-only cuspidal kernel: proof of `RationalCuspidalVanishingComparisonStatement`

Module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalVanishingComparisonProof`,
namespace `Langlands.HarishChandraSchwartz`.

## Result

`Langlands.HarishChandraSchwartz.rationalCuspidalVanishingComparison :
RationalCuspidalVanishingComparisonStatement.{u}`

The statement is in `RationalCuspidalConvergenceStatements.md`. It says: for a nonarchimedean
local field `F` (of either characteristic), a connected reductive `G` over `F` with maximal split
torus `i` and generic cocharacter `ν`, a compact open subgroup `K` of `G(F)` with
`G(F) = P₀(F) K` and a closed matrix representation `ρ`, an actual Schwartz function
`f ∈ RationalSchwartzSpace hKc hPK ρ` lies in the cuspidal submodule
`rationalCuspidalSubmodule hKc hPK ρ` if and only if
`RationalStandardConstantTermsVanish f` holds: for every proper standard root subset
`J = rootSet i ν I`, every Haar measure `ν_U` on `U_J(F)` and every pair `g = (g₁, g₂)`, the
normalized constant term `constantTermInd ν_U δ_{U_J} f g`, that is
`δ_{U_J}(m)^{1/2} ∫ f(g₂⁻¹ m u g₁) dν_U(u)`, vanishes. Membership in
`rationalCuspidalSubmodule` asks, in addition to this vanishing, that the integrals converge
absolutely; the theorem says that this convergence condition is automatic on the Schwartz space.

The theorem is proved at an arbitrary universe `u` and has no hypotheses. Its inputs are
published Library results imported by name. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

The Lean term is one application:

```
rationalConstantTermEstimate.cuspidalVanishingComparison
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence
```

1. `rationalConstantTermEstimate : RationalConstantTermEstimateStatement.{u}` (module
   `RationalConstantTermEstimateProof`) proves Waldspurger's Proposition II.4.5 on actual rational
   points.
2. `Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence :
   JointSpecialCompactBasisExistenceStatement.{u}` (module
   `Langlands.BruhatTits.SpecialCompact.JointBasisProof`) proves the existence of a special compact
   subgroup with its simultaneous standard basis and the accompanying Iwasawa and Cartan
   properties (Renard V.5.1–V.5.2).
3. `RationalConstantTermEstimateStatement.cuspidalVanishingComparison` (module
   `RationalConstantTermConvergenceReduction`) derives
   `RationalCuspidalVanishingComparisonStatement` from these two propositions. By its definition
   it is `RationalSchwartzConstantTermConvergenceStatement.vanishingComparison` (module
   `RationalCuspidalConvergenceStatements`) applied to
   `RationalConstantTermEstimateStatement.schwartzConstantTermConvergence` of the same two
   inputs, which proves `RationalSchwartzConstantTermConvergenceStatement`.

The implication `vanishingComparison` rewrites membership with
`mem_rationalCuspidalSubmodule_iff_constantTermInd` (module `RationalCuspidalSpace`), which
expresses it as integrability of every two-sided translate `v ↦ f(x v y)` on `U_J(F)` together
with vanishing of the normalized constant terms, for every proper `J` and every Haar measure. The
forward direction keeps the vanishing; the reverse direction supplies the integrability from the
radical convergence proposition and keeps the given vanishing.

The theorem adds no convergence, estimate or structural premise beyond those of the statement.
When the relative rank is zero there is no proper root subset, both sides hold for every `f`, and
the proof does not treat this case separately.

## Dependencies

All three imported modules, `RationalConstantTermConvergenceReduction`,
`RationalConstantTermEstimateProof` and `Langlands.BruhatTits.SpecialCompact.JointBasisProof`, are
in the Library.

## Scope and source

The statement is an internal formulation: it identifies the convergence-strengthened kernel
`rationalCuspidalSubmodule` with the vanishing of the normalized standard constant terms of
J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), 235–333 (literature id `waldspurger-2003-plancherel`), III.6,
printed pp. 271–272, using the convergence of Proposition II.4.5, printed pp. 262–263. It does
not compare this kernel with the full semistandard index or with the recursive projection of
VIII.2.1.
