# Assembly of the Galois-stable Iwahori chamber input from focused statements

This module states and proves `LocalSimplyConnectedUnramifiedChamberAssemblyStatement`: five
focused statements imply `LocalSimplyConnectedUnramifiedChamberStatement`. It is a conditional
reduction. It does not prove the chamber statement, because three of its inputs are new and
unproved, and the other two are published but not yet proved.

## Statement

`LocalSimplyConnectedUnramifiedChamberAssemblyStatement.{u}` is the implication

```
UnramifiedQuasiSplitStatement.{u} →
SpecialTorusExistenceStatement.{u} →
MaximalUnramifiedAffineWeylStatement.{u} →
UnramifiedTwistedChamberStatement.{u} →
LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u} →
LocalSimplyConnectedUnramifiedChamberStatement.{u}
```

with the inputs:

- `UnramifiedQuasiSplitStatement` (published, `Geometry/Building/UnramifiedQuasiSplitStatement`):
  every connected reductive group over `K = inertiaFixedField F` is quasi-split;
- `SpecialTorusExistenceStatement` (published, `Geometry/Building/UnramifiedSpecialApartmentStatement`,
  KP Proposition 9.3.4): every maximal `F`-split torus lies in a closed `F`-subgroup `T` whose
  scalar extension `T_K` is a maximal `K`-split torus;
- `MaximalUnramifiedAffineWeylStatement` (new, `Geometry/Building/MaximalUnramifiedAffineWeylStatement`,
  KP Proposition 6.3.13): for supplied building data over `K`, the affine roots form an affine
  root system and its affine Weyl group is realized by `N(K)`;
- `UnramifiedTwistedChamberStatement` (new, `Geometry/Building/UnramifiedTwistedChamberStatement`,
  KP Proposition 9.10.4 as used in the proof of Theorem 10.6.1): on the building data of a
  `Γ`-stable apartment class of a special torus, every finite-level crossed homomorphism
  `c : Γ → G(K)` has a chamber stable under `y ↦ c(σ) · σ(y)`;
- `LocalSimplyConnectedUnramifiedIwahoriModelStatement` (new,
  `GroupScheme/SimplyConnected/LocalUnramifiedIwahoriModelStatement`, KP 9.2.5, 8.3.13, 4.1.12,
  9.3.26): for simply connected `G`, a `Γ`-stable chamber of any building data with semilinear
  Galois data has a smooth `𝒪[F]`-model with connected special fibre whose `𝒪_K`-points are
  its stabilizer.

## Proof

The theorem `localSimplyConnectedUnramifiedChamberAssembly` proves the implication at arbitrary
universe `u`. Fix `F`, an affine `G` with `IsSimplyConnected G`, and the five inputs.

1. *Building data and Galois data.* `G` is connected reductive (`IsSimplyConnected.isSemisimple`,
   `IsSemisimple.isConnectedReductive`), hence smooth, and `exists_maximalSplitTorus` gives a
   maximal `F`-split torus `S`. `SpecialTorusExistenceStatement` gives a closed `F`-subgroup
   `iT : T → G` containing `S` with `T_K` maximal `K`-split, and
   `connectedReductiveFieldExtensionStatement` shows that `G_K` is connected reductive.
   `UnramifiedBuildingDescent.exists_omegaCompatible`, applied to `UnramifiedQuasiSplitStatement`
   and the published proof `quasiSplitIntegerApartmentExistence`, gives an apartment class `D`
   of `T_K` with a centralizer datum `C` and V 6 (`h6`), and
   `MaximalUnramified.galoisStable_of_isOmegaCompatible` shows that `D` is `Γ`-stable (`hD`).
   The witnesses for the building data and the semilinear Galois data are
   `UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6` and
   `UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD`, the same construction as in
   the published `unramifiedBuildingDescentReduction`.
2. *The `Γ`-stable chamber (clauses 3 and 4).* `UnramifiedTwistedChamberStatement` applied to
   the constant map `c = 1` (a crossed homomorphism because `rationalConjugate` preserves `1`,
   and trivial on the fixing subgroup of the finite-dimensional field `E = ⊥`) gives a chamber
   `Y₀` with `(fun y => 1 • action σ y) '' Y₀ = Y₀`; `one_smul` turns this into
   `action σ '' Y₀ = Y₀`.
3. *The Iwahori model (clauses 1, 2 and 5).* `LocalSimplyConnectedUnramifiedIwahoriModelStatement`
   applied to these data, `Y₀` and its `Γ`-stability gives the model `M`, its smoothness, the
   connectedness of its special fibre and the stabilizer equivalence.
4. *Twisted-stable chambers (clause 7).* This is `UnramifiedTwistedChamberStatement` for the
   given cocycle, with the same data.
5. *Chamber transitivity (clause 6).* Write `Y₀ = g₀ · Ca₀` and `Y = g · Ca` with chambers
   `Ca₀`, `Ca` of the apartment (definition of `IsChamber`). By `MaximalUnramifiedAffineWeylStatement`
   the affine roots form an affine root system, so the published theorem
   `affineChamberSimpleTransitivity` gives `w ∈ W(Ψ)` with `w '' Ca₀ = Ca`, and the same
   statement gives `n ∈ N(K)` with `normalizerAffineEquiv n = w`. Then
   `g n g₀⁻¹ · Y₀ = g · (n · Ca₀) = g · Ca = Y`, by `mul_smul`, `inv_smul_smul`,
   `KPApartmentData.normalizerAffineEquiv_apply` and
   `IntegerValuationBuildingData.normalizer_smul_apartmentMap` (`n · [x] = [n · x]`).

The proof uses no proof of `LocalSimplyConnectedUnramifiedIntegralTwistStatement`,
`LocalSimplyConnectedUnramifiedCocycleVanishingStatement`,
`LocalSimplyConnectedGaloisCocycleVanishingStatement` or
`LocalSimplyConnectedCocycleVanishingStatement`.

## Provenance

This is an internal reduction for Task 5999. Its mathematical content is the decomposition of
the chamber statement into the building facts cited in its Markdown: Kaletha–Prasad
Proposition 6.3.13 with Lemma 1.3.17 (chamber transitivity of `N(K)` through `W(Ψ)`, the
apartment form of 4.1.12(4)), Proposition 9.10.4 with the proof of Theorem 10.6.1 (stable and
twisted-stable chambers), and 9.2.5, Theorem 8.3.13, 4.1.12(1), Remark 4.1.13 and 9.3.26
(the Iwahori model). The construction of the building data from a special torus is the
Library's, taken from `UnramifiedBuildingDescentReduction`.
