# Normalized characters on the original represented common Levi

This internal adapter compares scalar characters on every rational point of the original target common Levi `D.L'` of a `GeometricLemmaIntersectionDatum`. The field has universe `u`; no representation carrier or finiteness condition occurs. The original datum, representative `z`, common Levi and its inclusion in the ambient group are retained.

Use the notation of `RepresentedGeometricLemmaHaarBalance`: `U` and `V` denote the forward target and source radical moduli, `A` the source endpoint modulus, `B` the distinct target endpoint modulus and `C` the common-radical modulus, all pulled to the same original common-Levi point. Write `D₀` for the full original target correction-intersection modulus, pulled back through `D.targetCommonLeviPointsEquiv`. Its subgroup is literally

```text
pointImage (rQ ≫ q) ∩ z⁻¹ pointImage p z.
```

The definition `normalizedCommonLeviCoefficientCharacter` is the scalar expression

```text
η = sqrt(U) / D₀ · sqrt(V).
```

Every positive square root is embedded in complex units. The denominator is the full correction-intersection modulus, without a square root. `normalizedCommonLeviEndpointCharacter` is

```text
ζ = sqrt(B) · sqrt(A)⁻¹.
```

The ambient rational-point group has its canonical locally compact nonarchimedean topology, and the field topology is Hausdorff. The first two theorems require no dynamic realization, relative-root system or character-detection hypothesis.

`normalizedCommonLeviCoefficientCharacter_eq_original` identifies `η` with the original outer target Jacquet inverse half, times the full ratio `U / D₀`, times the original source inducing half pulled through `D.e` and the original source-Levi inclusion. It rewrites with `targetInverseHalfCharacter_commonLevi` and `inducingHalfCharacter_commonLevi`, then uses the square of the canonical positive half-character to cancel one target half. This is an equality of characters on the common Levi. It does not yet identify the Haar ratio arising from the compact quotient integral or compare the associated representations.

`normalizedCommonLeviEndpointCharacter_eq_original` identifies `ζ` with the product of the actual inner target inducing half for `D.q', D.lQ', D.rQ'` and the actual inner source Jacquet inverse half for `D.p', D.l', D.r'`, transported by the supplied actual map `D.e`. The proof applies `targetHalfCharacter_commonLevi` and `sourceInverseHalfCharacter_commonLevi`. The topology, affinity, local compactness and nonarchimedean-group instances of the original ambient source and target Levis are derived from their represented parabolic triples.

For `normalizedCommonLeviCoefficientCharacter_eq_epsilonEndpoints`, ambient rational points are additionally second countable and a simultaneous `R : D.DynamicRealization` is supplied. The proof rewrites `D₀ = A · C` using the original target-intersection factorization and rewrites both original epsilon corrections with their full forward formulas. The resulting equality

```text
η = (originalSourceCorrectionCharacter · originalTargetCorrectionCharacter) · ζ
```

is a commutative complex-unit identity. The private algebra lemma inserts `sqrt(B)⁻¹ · sqrt(B)` and reorders factors, while `positiveHalfCharacter_sq` recovers the two factors of the denominator. No common-Levi balance or cancellation is assumed for this factorization.

Finally, `normalizedCommonLeviCoefficientCharacter_eq_endpoints` works over a nonarchimedean local field with smooth affine ambient group. Besides `R`, it retains `HasRelativeRootSystem` for the actual transported ambient common torus and injectivity of algebraic-character restriction to `D.targetCommonTorusHom`. It derives ambient second countability, applies the epsilon-product factorization and the existing conditional original correction-product theorem, and obtains `η = ζ` on the entire original common Levi. The torus closed-immersion instance comes from its original ambient maximal-split-torus law.

The provenance is internal, combining the previously constructed original correction and endpoint character identities with commutative unit algebra, in the same scalar pattern as `RationalGeometricNormalizedCoefficientCharacter`. Existence of the simultaneous dynamic realization, the relative-root input and character detection remain explicit obligations. Extension from the common Levi to the full target parabolic intersection, identification with the actual compact-quotient action, construction of a natural representation isomorphism and the exact closed `RepresentedGeometricLemmaOrbitComparisonStatement.{u,v}` remain outside this unit. Its published statement and hypotheses are unchanged.
