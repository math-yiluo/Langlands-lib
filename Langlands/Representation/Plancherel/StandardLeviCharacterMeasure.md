# I.1 character and orbit measures on the literal standard Levi

Worker 270. Namespace `Langlands.Plancherel`.

This derived adapter transports the published I.1 character and VI.3 orbit measures to the literal standard Levi subgroup used by the actual wave-packet integral. It does not change the inducing representation to a representation on a dynamic Levi.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)* (2003), registered source `waldspurger-2003-plancherel`, SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`. I.1, printed p.239 (PDF p.5), fixes probability Haar measure on the split-component character group and local measure preservation for restriction. VI.3, printed p.302 (PDF p.68), fixes orbit measure by local measure preservation of the twisting map. The cardinality formulas here are derived consequences of those conventions and the existing finite-cover constructions, rather than formulas printed separately in the source.

The new constructions reuse `RationalCharacterHaar`, `RationalNormalizedOrbitMeasure`, `RationalOrbitIntegration`, `DiscreteSeriesOrbitMeasure`, and the class and central-quotient transports of `RationalLeviDiscreteSeriesOrbitFiniteness`. All lemmas in this pair are proved. No Schwartz estimate or membership assertion is proved here.

## Actual data and hypotheses

The field `F : Type u` has the shared `IsNonarchimedeanLocalField` structure, with arbitrary characteristic. The representation-carrier universe `uV` is independent of `u`. The ambient group scheme is affine and locally of finite type. Write

- `L = Standard.leviScheme i ν (rootSet i ν I)` for the intrinsic Levi scheme;
- `M = standardLeviPoints i ν (rootSet i ν I)` for the literal subgroup of `G(F)`;
- `eM = leviRationalPointHomeomorph i ν I : L(F) ≃ₜ* M`;
- `s : T.toGrp ⟶ L` for the displayed actual split-component morphism, with `hs : IsSplitComponent s` and affine `T`;
- `CL = (rationalPoints.map s).range` and `CM = rationalLeviSplitCenter I s`.

The standard connected reductive application supplies maximal split torus and generic cocharacter hypotheses. These are not needed by the transport identities themselves. The adapter takes normality instances for `CL` and `CM`; they follow from `hs.isCentralSplitTorus.isCentral.range_le_center` and `rationalLeviSplitCenter_le_center I s hs`, respectively, by `Subgroup.normal_of_le_center`. They impose no additional mathematical condition. The literal quotient `M / CM` has its displayed Borel measurable space and Haar measure `mu`. The intrinsic quotient uses its Borel measurable space.

The actual-image premise `hindex : (RenardCartan.splitValuationImage s).FiniteIndex` is retained explicitly. It is an unresolved structural proof obligation in the standing program, not a permitted permanent external structural input. The imported finite-kernel and finite-stabilizer theorems use this premise. No separate self-twist finiteness assumption is mathematically necessary: `finite_standardLeviDiscreteSeriesStabilizer` derives it. Some comparison lemmas bind a `Finite` instance for that stabilizer to elaborate the existing integral measure; callers can use this theorem.

## Character scale

`standardLeviUnitaryCharacterHomeomorph I` is exactly the existing `unitaryUnramifiedCharactersHomeomorph eM` on the intrinsic rational norm-character family, with its codomain written as the literal family `leviRationalNormCharacters i ν I`. It sends `z` to `z ∘ eM⁻¹`.

Put `K_s = ker (rationalUnitaryUnramifiedCharacterRestrict s)` and let `lambdaL = rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex`. The new `standardLeviUnitaryUnramifiedCharacterHaar` is

\[
 \lambda_M=(eX)_*\lambda_L.
\]

The Haar instance follows by transport along the continuous multiplicative equivalence. `standardLeviUnitaryUnramifiedCharacterHaar_univ` gives its exact total mass `|K_s|`, using the imported character mass formula. Its finite-measure instance follows immediately. It is generally not probability Haar. The scale comes from I.1 restriction, with no freely chosen scalar.

## Central quotient and auxiliary classes

`standardLeviCentralQuotientHomeomorph` is the induced equivalence `eQ : L(F)/CL ≃ₜ* M/CM`. `standardLeviIntrinsicQuotientHaar` is `muL = (eQ⁻¹)_* mu`; `map_standardLeviIntrinsicQuotientHaar` proves `(eQ)_* muL = mu` by the measurable equivalence inverse law. Haar measure transports along the group homeomorphism.

For a discrete-series class `omega` of `M` modulo the displayed `CM` and `mu`, `standardLeviIntrinsicDiscreteSeriesClass` pulls its class back to `L(F)` modulo `CL` and `muL`. The imported square-integrability transport justifies this construction; no new square-integrability premise on the pullback is imposed. The main inducing representation remains on `M`.

`standardLeviCharacterHomeomorph_map_stabilizer` identifies the intrinsic and literal self-twist groups. Its proof uses injectivity of class pullback and its compatibility with twisting in both directions. `standardLeviStabilizer_card` follows from the resulting subgroup equivalence. `finite_standardLeviDiscreteSeriesStabilizer` transports the imported intrinsic finite-stabilizer result.

`standardLeviDiscreteSeriesOrbitHomeomorph` composes the existing orbit-stabilizer homeomorphisms with the quotient equivalence induced by `eX`. The proved orbit-map formula sends `omegaL ⊗ z` to `omega ⊗ eX(z)`. No topology on the whole smooth dual is needed.

## Orbit measure and finiteness reuse

`standardLeviNormalizedDiscreteSeriesOrbitMeasure` is the pushforward along this orbit homeomorphism of `rationalNormalizedDiscreteSeriesOrbitMeasure s ... muL hindex omegaL`. Its finite-measure instance reuses `isFiniteMeasure_rationalNormalizedDiscreteSeriesOrbitMeasure` through pushforward; the orbit finiteness argument is not rebuilt.

`standardLeviNormalizedDiscreteSeriesOrbitMeasure_eq` proves that this transported measure is exactly the existing `discreteSeriesOrbitMeasure` of the literal orbit with character measure `lambdaM`. Its proof compares measurable sets using the imported orbit pushforward formula, the equality of stabilizer cardinalities and the commuting orbit-map square. The `_eq_smul_map` and `_univ` lemmas record

\[
 \eta_M=|S_\omega|^{-1}(p_M)_*\lambda_M,
 \qquad \eta_M(O)=|K_s|/|S_\omega|.
\]

Thus this measure is not generally a probability measure. `isLocallyMeasurePreserving_standardLeviNormalizedDiscreteSeriesOrbitMap` specializes the existing finite-fiber local-preservation theorem. `isFiniteMeasure_standardLeviOrbitMeasure` transfers the already obtained finite-measure instance to the exact measure used in the actual wave-packet integral.

This pair discharges the intrinsic-to-literal character/orbit transport. It does not discharge `hindex`, construct new coefficient estimates, compare dynamic and standard parabolics, or prove Schwartz membership, synthesis continuity, inversion or Plancherel.
