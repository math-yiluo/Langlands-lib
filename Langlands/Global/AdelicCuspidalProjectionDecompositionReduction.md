# Proof of the reduction of the cuspidal projection decomposition

Module `Langlands.Global.AdelicCuspidalProjectionDecompositionReduction` proves
`Langlands.Global.CuspidalProjectionDecompositionReductionStatement` (module
`AdelicCuspidalProjectionDecompositionReductionStatement`) as the theorem
`Langlands.Global.cuspidalProjectionDecompositionReduction`. Given the four inputs
`ConstantTermAutomorphyStatement`, `CuspidalProjectionExistenceStatement`,
`ParabolicCuspidalVanishingStatement` and `AutomorphicExponentDecompositionStatement`, it
derives `CuspidalProjectionDecompositionStatement`.

## Auxiliary results (private to the module, namespace `Langlands.Global.StandardParabolicFamily`)

- `leviPairingIntegrand_sub`: the norm-one Levi pairing integrand is additive in the tested
  function; for a difference it is the difference of the integrands.
- `sub_mem_cuspidalAnnihilator_of_isCuspidalProjection`: if `ψ` and `ψ'` are cuspidal
  projections of the same `φ` along `Q`, then `ψ' - ψ` lies in the fibrewise cuspidal
  annihilator `InCuspidalAnnihilator` for `Q`. For each Levi cusp form `t` and each `g`, the
  integrand of `ψ' - ψ` is integrable as a difference of integrable functions, and its integral
  is `(φ, t) - (φ, t) = 0` by the two pairing identities.
- `isIwasawaCompact_of_minimal`: `P₀(𝔸)K = G(𝔸)` for the minimal standard parabolic implies
  `P_R(𝔸)K = G(𝔸)` for every standard `R`. The containment `P₀ ⊆ P_R` of standard parabolics
  (`le_iff_range_le`) factors `P₀ → G` through the closed subgroup `P_R → G`
  (`SubgroupFunctor.rangeFactor`), and `IsIwasawaCompact.of_comp` applies.
- `eq_of_isCuspidalProjection_of_pos`: for an embedding of positive size, two cuspidal
  projections of the same function agree. The difference `ψ' - ψ` is automorphic on
  `U_Q(𝔸)M_Q(F)\G(𝔸)` (the automorphic functions form the submodule `automorphicFunctionsOn`),
  hence left invariant, continuous and of moderate growth; it is cuspidal along `Q`
  (`isCuspidalAlong_sub`). For `R < Q` its constant term along `R` is zero, which lies in the
  annihilator; for `R = Q` its constant term is itself (`constantTerm_eq_self_of_automorphicOn`),
  which lies in the annihilator by the previous item. `ParabolicCuspidalVanishingStatement`
  then gives `ψ' - ψ = 0`.
- Size zero (`section RankZero`). `Langlands.Global.subsingleton_adelicGroupPoints_of_rank_zero'`: a group with a
  closed embedding into `GL_0` has a single adelic point, since the adelic matrix map is a
  closed embedding (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`) into the trivial
  group of `0 × 0` invertible matrices. `isAutomorphicFunctionOn_one_of_subsingleton`: on such a
  group the constant function `1` is automorphic for every left subgroup, archimedean subgroup
  and representation. Its slices are constant, hence plot-smooth; its right translates span a
  line; the center of the enveloping algebra acts on the finite-dimensional space of
  plot-smooth functions on the one-point group `G(F_∞)`, so a cofinite ideal annihilates the
  constant slice (`Langlands.exists_cofiniteIdeal_annihilates_of_finite_centralOrbit`); and
  `|1| ≤ 1 · ‖g‖^0`. `isLeviCuspidal_one_of_rank_zero`: the constant function is cuspidal on
  every standard Levi `M_J`, because every point of `M_J` over every test scheme is trivial (its
  image in `GL_0`, through the closed embedding `M_J → P_J → G → GL_0`, is the unique point), so
  every parabolic subgroup of `M_J` is all of `M_J` and the cuspidality condition is vacuous.
  `eq_of_isCuspidalProjection_of_rank_zero`: pairing `ψ' - ψ` with the constant Levi cusp form
  on the one-point norm-one quotient gives the constant integrand `ψ'(g) - ψ(g)`; if it were
  nonzero, integrability would make the Haar measure finite, and its nonzero total mass
  (`normOneRationalQuotientHaarMeasure_ne_zero`) would make the integral nonzero.

## The theorem

`cuspidalProjectionDecompositionReduction`: for `Q ≤ P` and `φ` automorphic on
`U_P(𝔸)M_P(F)\G(𝔸)`, the constant term `C_Qφ` is automorphic on `U_Q(𝔸)M_Q(F)\G(𝔸)` by
`ConstantTermAutomorphyStatement`, and `CuspidalProjectionExistenceStatement` gives a cuspidal
projection `ψ` of it. Uniqueness follows from `eq_of_isCuspidalProjection_of_pos` or
`eq_of_isCuspidalProjection_of_rank_zero`, according as the embedding has positive size or
size zero. `AutomorphicExponentDecompositionStatement`, applied to the automorphic function
`ψ`, gives a finite family of automorphic summands with unnormalized exponents; since `ψ` is
cuspidal along `Q`, so are the summands, and these data form an `IsExponentDecomposition`.

The argument is internal. It follows the structure of Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), §6.2, pp. 201–202 (constant terms and the cuspidal
projection (6.8)) and §6.3, p. 203 (the decomposition (6.10)), with uniqueness from the
vanishing criterion (8.1) and Mœglin–Waldspurger I.3.4.
