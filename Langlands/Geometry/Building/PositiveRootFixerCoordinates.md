# Positive root fixers of a set from ordered root coordinates

Fix a cocharacter `ν` of the split torus `S` and a non-empty `Ω ⊆ A(S)`. Write
`b > 0` for relative roots `b` with `⟨b, ν⟩ > 0`, the set `positiveRelativeRoots i ν`.
This module proves

```text
⋂_{x ∈ Ω} ⟨U_{b,x,0} : b > 0⟩ = ⟨U_{b,Ω,0} : b > 0⟩.
```

Here `U_{b,x,0} = D.chamberRootGroup x false b` (the depth-zero filtration group
`D.filtration x b 0`), and `U_{b,Ω,0} = D.rootFixer b Ω = U_b(k) ∩ ⋂_{x ∈ Ω} U_{b,x,0}`.
The cocharacter `ν` need not be generic.

## Declarations

* `KPApartmentData.iSup_rootFixer_le_iInf_iSup_chamberRootGroup`: for any `Ω`,
  `⨆ b > 0, D.rootFixer b Ω ≤ ⨅ x ∈ Ω, ⨆ b > 0, D.chamberRootGroup x false b`.
* `KPApartmentData.iInf_iSup_chamberRootGroup_le_iSup_rootFixer`: the reverse
  inclusion for non-empty `Ω`. Its hypotheses are:
  * ordered root injectivity `RelativeRoot.OrderedRootPointInjectivity i`;
  * the extended affine roots form an affine root system in the sense of
    `IsAffineRootSystemWithRankZero` (any rank, rank zero allowed), with
    derivative set `Set.range (rootForm i)` (`hsys`, `hderiv`);
  * finiteness of the relative roots.
* `ParahoricBuildingData.iInf_iSup_chamberRootGroup_eq_iSup_rootFixer`: for
  `P : ParahoricBuildingData G` with `hP : P.SatisfiesApartmentAxioms` and
  non-empty `Ω`,
  `(⨅ x ∈ Ω, ⨆ b : positiveRelativeRoots P.i ν, P.apartment.chamberRootGroup x false b)
  = ⨆ b : positiveRelativeRoots P.i ν, P.apartment.rootFixer b Ω`.
* `PositiveRootFixerCoordinatesStatement`: this equality as a proposition. It
  quantifies over every nonarchimedean local field `F`, affine group scheme `G`
  over `F` in universe `u`, `P : ParahoricBuildingData G` with
  `P.SatisfiesApartmentAxioms`, cocharacter `ν` of `P.S` and non-empty `Ω`.
* `positiveRootFixerCoordinates : PositiveRootFixerCoordinatesStatement.{u}`:
  its proof.

## Implemented proof

**`⊇`.** If `u ∈ U_{b,Ω,0}` and `x ∈ Ω`, then `u ∈ U_{b,x,0}` (`mem_rootFixer`).
So each term of the left supremum lies in the corresponding term at `x`
(`iSup_mono`), and `le_iInf₂` gives the inclusion.

**`⊆`.** The indivisible positive roots form a finite subset of the relative
roots. `Set.Finite.fin_param` gives an injective enumeration
`a : Fin n → characterLattice S` of them. At every point `x`,
`range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup` identifies
`⟨U_{b,x,0} : b > 0⟩` with the set of ordered products `∏_j t_j`,
`t_j ∈ U_{a_j,x,0}`. It needs `hsys` and `hderiv`. Note that `U_{a_j,x,0}`
already contains the `U_{2a_j,x,0}` part.

Let `g` lie in the left-hand side. Pick `y ∈ Ω` and write `g = ∏_j t_j` with
`t_j ∈ U_{a_j,y,0}`. For any `x ∈ Ω` also write `g = ∏_j s_j` with
`s_j ∈ U_{a_j,x,0}`. Each factor lies in the root group `U_{a_j}(k)`
(`filtration_le_rootGroupPoints`). Ordered root injectivity, applied to the two
coordinate families in `∏_j U_{a_j}(k)`, gives `t_j = s_j`. Hence
`t_j ∈ U_{a_j,x,0}` for all `x ∈ Ω`, that is `t_j ∈ U_{a_j,Ω,0}`. Every `a_j`
is a positive relative root, so each `t_j` lies in
`⨆ b > 0, D.rootFixer b Ω`, and so does the product `g` (`list_prod_mem`).

**Supplied data.** For `P` the hypotheses are discharged as follows:
* ordered root injectivity by
  `RelativeRoot.orderedRootPointInjectivity_of_hasOppositeFactorPairs`, with
  the split torus and `ParahoricBuildingData.hasOppositeFactorPairs`;
* `hsys` and `hderiv` by the fields `isAffineRootSystem_extendedAffineRoots` and
  `derivativeRoots_extendedAffineRoots` of `hP`;
* finiteness of the relative roots by `finite_relativeRoots` of the split torus.

Smoothness of `G` comes from `P.isConnectedReductive.smooth`.

## Provenance and scope

This is an internal lemma for KP Lemma 7.7.4 (Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach*, printed pp. 268–269). It is the identity
`U^+_{Ω'} = ⋂ U^+_{Ω_i}` used twice in KP's proof: as
`U^-_x ∩ U^-_Ω = U^-_{Ω ∪ {x}}` in the induction step, and as
`⋂ U^+_{Ω_i} = U^+_Ω` in the limit step. Here `U^+_Ω` is the subgroup generated
by the `U_{b,Ω,0}` for `ν`-positive `b`. KP justify it by the unique product
decomposition of Proposition 7.3.12 and Proposition 2.11.3(2). The Lean proof
uses the Library's ordered root injectivity and ordered-product collection
instead. No external assertion beyond the Library is introduced.
