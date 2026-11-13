# Proof of Renard VII.3.5 (iii)

Lean module: `Langlands.Representation.Intertwining.PQIntertwiningOuterLeviProof`.

The theorem `pqIntertwiningOuterLevi : PQIntertwiningOuterLeviStatement.{u, v}` proves the
published statement `PQIntertwiningOuterLeviStatement` (Renard 2026, French version of
9 July 2026, VII.3.5 Proposition (iii), printed pp.238–240 / PDF pp.244–246): for parabolics
`P₁ = MN₁ ⊂ Q₁ = LU₁` and `P₂ = MN₂ ⊂ Q₂ = LU₂` of a connected reductive `G` over a
nonarchimedean local field, with the same Levi subgroups `M` and `L`, opposites `P̄₁`, `Q̄₁`,
and a parabolic `P' = MN'` of `L` with `P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)`:

1. every Haar measure on `W = Ū₁(F) ∩ U₂(F)` has a compatible Haar measure on
   `V = N̄₁(F) ∩ N₂(F)`;
2. every `f ∈ i_{P₁}^G(σ)` has a stage transform `F ∈ i_{Q₁}^G(i_{P'}^L(σ))` with
   `F(g)(x) = δ_{U₁}(x)^{-1/2} f(xg)`;
3. if `X = i_{P'}^L(σ)` is `Q₁Q₂`-regular, then `σ` is `P₁P₂`-regular and, for compatible Haar
   measures and integral-normalized operators `J = J_{P₂|P₁}(σ)` (on `V`) and
   `J_Q = J_{Q₂|Q₁}(X)` (on `W`), `J_Q F` is the stage transform of `J f` along `Q₂`.

The Markdown of the statement records its source correspondence; the proof route below differs
from Renard's in the regularity and operator steps, as explained in the helper modules.

## Proof

After introducing the data (with `L(F)` and `M(F)` carrying their canonical topologies):

- `V = W` by `outerRadical_inf_eq` (module `PQOuterLeviRadicals`); `V` is closed as an
  intersection of closed rational-point images.
- Clause 1: given a Haar measure on `W`, `exists_haar_integral_eq_of_subgroup_eq` (module
  `PQOuterLeviOperator`) transports it to `V` with the same integrals of all functions.
- Clause 2: `F = Φ₁ f`, where `Φ₁ = leviInductionStagesIso` for `P₁ ⊂ Q₁` (module
  `LeviInductionStagesFormula`); its formula is `leviInductionStagesIso_eval'`.
- Clause 3, regularity: `outer_isPQRegular` (module `PQOuterLeviRegularity`).
- Clause 3, operators: a given `F` with the stage formula equals `Φ₁ f`
  (`leviInductionStages_ext`). By `outer_intertwiner_stages` (module `PQOuterLeviOperator`),
  `J_Q (Φ₁ f) = Φ₂ (J f)`, where `Φ₂` is the stage isomorphism for `P₂ ⊂ Q₂` (its hypotheses
  are `outer_levi₂_eq` and `outer_parabolic₂_eq`). The formula of `Φ₂`
  (`leviInductionStagesIso_eval'`) gives the claim, after rewriting the embedding of `L`
  through `Q₂` as the one through `Q₁` (`lQ₂ ≫ q₂ = lQ₁ ≫ q₁`).

## Helper modules

`PQOuterLeviRadicals`, `PQOuterLeviSupport`, `PQOuterLeviOperator`, `PQOuterLeviRegularity`
(this proof), and `HaarTransportComparison`, `LeviInductionStagesFormula`,
`PQIntegralUniqueness` (written by Worker 115 for part (ii), used here unchanged).
