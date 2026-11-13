# Proof of Renard VII.3.5 (ii): intertwining operators and induction in stages

Author: Worker 115 (supporting modules shared with Worker 86). Module
`Langlands.Representation.Intertwining.PQIntertwiningInnerLeviProof`.

The theorem `Langlands.Aubert.General.RepresentedParabolic.pqIntertwiningInnerLevi` proves
the published statement `PQIntertwiningInnerLeviStatement` (module
`Langlands.Representation.Intertwining.PQIntertwiningLeviStatements`). That statement is
Renard VII.3.5 Proposition (ii): David Renard, *Représentations des groupes réductifs
p-adiques*, French version of 9 July 2026, printed pp.237–240 / PDF pp.243–246. It keeps
the statement's universe parameters `u v` and adds no hypotheses. The Lean build checks it
with only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

The setting has:

- `P₁ = MN₁` and `P₂ = MN₂`, represented parabolics of `G` with the same embedded Levi;
- `P̄₁ = MN̄₁`, an opposite of `P₁`;
- `Q = LU` with `P₁(F), P₂(F) ⊂ Q(F)`;
- parabolics `P₁'`, `P₂'` and `P̄₁'` of `L` with `Pᵢ'(F) = Pᵢ(F) ∩ L(F)`;
- `V = N̄₁(F) ∩ N₂(F)`, `V' = N̄₁'(F) ∩ N₂'(F)` and `c = δ_U^{1/2}` on `L(F)`.

Under these hypotheses, the statement asserts:

1. every Haar measure `haar'` on `V'` has a compatible Haar measure `haar` on `V`, that is,
   `∫_{V'} φ(emb x) dhaar' = ∫_V φ dhaar` for continuous compactly supported `φ`;
2. for each smooth `σ`:
   - every `f ∈ i_{P₁}^G(σ)` has an `f̃ ∈ i_Q^G(i_{P₁'}^L(σ))` with
     `f̃(g)(x) = c(x)⁻¹ f(emb(x) g)`;
   - if `σ` is `P₁P₂`-regular, then it is `P₁'P₂'`-regular. Moreover, for compatible Haar
     measures and integral-normalized `J = J^G_{P₂|P₁}(σ)` and `J' = J^L_{P₂'|P₁'}(σ)`,
     `J'(f̃(g))(x) = c(x)⁻¹ J(f)(emb(x) g)` whenever `f̃` satisfies the formula.

## The proof

The theorem introduces the statement's variables. It installs the instances that the
statement binds with `haveI`/`letI`: the point topologies on `G(F)`, `L(F)` and `M(F)`, and
local compactness and the nonarchimedean property of `L(F)`. It also derives
`hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂` from `h₂₁`, `hM₁` and `h₂₁'`. Then:

- **The domain.** `innerIntegrationDomain_eq_map` (module `InnerLeviIntegrationDomain`)
  gives `V = emb(V')`, and `exists_leviSubgroupEquiv` gives an isomorphism of topological
  groups `e : V' ≃ₜ* V` with `e x = emb x`.
- **Clause 1.** Take `haar = e_* haar'`. `map_isHaarMeasure_integral_eq` (module
  `HaarTransportComparison`) shows that `haar` is a Haar measure and that
  `∫_{V'} φ(e x) dhaar' = ∫_V φ dhaar` for all `φ`.
- **Existence of `f̃`.** Take `f̃ = Ψ₁(f)`, where `Ψ₁ = leviInductionStagesIso` (module
  `LeviInductionStagesFormula`). The formula is `leviInductionStagesIso_eval'`. The
  statement's hypothesis `hPL₁` has the intersection in the other order, so the proof
  passes `hPL₁.trans (inf_comm _ _)`.
- **Regularity.** `innerLevi_isPQRegular` (module `InnerLeviRegularity`) shows that
  `P₁P₂`-regularity of `σ` implies `P₁'P₂'`-regularity.
- **The operator identity.** Fix compatible Haar measures `haar'` and `haar`. `G(F)` is
  second countable (`RationalPointFamily.reductiveRationalPoint_secondCountable`), and `V`
  is closed (an intersection of two closed radical point groups). So
  `haar_eq_map_of_integral_eq` gives `haar = e_* haar'`. The compatibility identity serves
  as its hypothesis, after rewriting `φ ∘ emb = φ ∘ e`. Then
  `innerLevi_integralIntertwiner_formula` (module `InnerLeviOperatorIdentity`) gives the
  identity. Its hypothesis `V' ⊆ N₂'(F)` is `inf_le_right`.

## Relation to Renard's argument

For the operator identity, Renard restricts `f ∈ F̃^{<1}_{P₁P₂}` to `L` through
`f ↦ f̃(1)`, evaluates `i_Q^G(J')(f̃)` at `g = 1`, compares the integrals over
`N̄₁ ∩ N₂ = (N̄₁ ∩ L) ∩ (N₂ ∩ L)`, and concludes by the uniqueness in VII.3.4. The Lean proof
follows this route.

- The uniqueness is formalized by `integralIntertwiner_unique` (module
  `PQIntegralUniqueness`). It is derived from `IsPQRegular` and Frobenius reciprocity, and
  it does not use the unproved explicit-integral statement of VII.3.4.
- The identification of the integration domains (`InnerLeviIntegrationDomain`) and the
  vanishing of `c` on `N₂'(F)` are proved separately. Renard uses both without comment.
- So is the transfer of the boundary condition (`InnerLeviBoundaryTransfer`, through
  `mem_innerBoundaryVanishing_of_map`).

For regularity, Renard compares the Bruhat-cell ideals `I^{P₂,w̄}_σ`. The Lean proof
instead works with the Library's `IsPQRegular`, phrased through the quotient
`r_{P₂} i_{P₁}(σ) / F^{<1̄}_{P₁P₂}`. It uses the `M(F)`-equivariant surjection between
those quotients that `T f = f̃(1)` induces (see `InnerLeviRegularity.md`).

## Supporting modules

All are in `Langlands/Representation/Intertwining/` and each has paired Markdown:
`PQIntegralUniqueness`, `LeviInductionStagesFormula`, `HaarTransportComparison`,
`InnerLeviIntegrationDomain`, `InnerLeviBoundaryTransfer`, `InnerLeviOperatorIdentity` and
`InnerLeviRegularity`. The first three are shared with the proof of part (iii)
(`PQIntertwiningOuterLeviProof`, Worker 86).
