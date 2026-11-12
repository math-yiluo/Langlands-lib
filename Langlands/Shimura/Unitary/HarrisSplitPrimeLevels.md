# Harris's levels at a prime split in the imaginary quadratic field

Author: Worker 19.

This module constructs the `p`-adic level subgroups of Harris (1999), (4.1),
for the unitary similitude group of the published Harris setup, through the
identification `GG(ℚ_p) ≅ (ℚ_p ⊗_{F, u} A)ˣ × ℚ_pˣ` of
`HarrisSplitPrimePoints`, which it upgrades to an isomorphism of topological
groups using `ImaginaryQuadraticSplitTopology` (submitted together with this
module). It then places these levels in the finite adelic points, as the
levels `K_p × K^p`, and identifies the Harris level tower at such levels, with
`K_p` fixed, with the published Harris tower away from `p`.

## Source

Harris (1999), Section 4, printed p. 309 (PDF p. 11), assumes that `p` splits
in the imaginary quadratic field `𝒦₀` and writes the `p`-component of the level
subgroup of `GJ(A_f)` as

"(4.1) `K_p = C_v × ∏_{j>1} C^(j) × ℤ_pˣ`",

where `C_v ⊂ (𝒟_1)ˣ` is an open compact subgroup "which we allow to vary,
whereas `C^(j) ⊂ (𝒟_j)ˣ` will be fixed; we are implicitly identifying
(4.2) `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ` as in [H2, Appendix, A.1]". The full level
is `K' = K'^p × K_p`, and `K(N, m)` is defined in the same way from
`K(N)_p = C_v^{N,0} × ∏_{j>1} C^(j) × ℤ_pˣ` and a level `K(m)^p` away from
`p`. Proposition 4.4 lets `K(N, m)^p` vary, with `GG(A_f^p)`-equivariance.
Harris (1998), Appendix, printed p. 206 (PDF p. 30), gives the same
factorization (A.2) of the `p`-level of `GG`, through (A.1).

Here `C` stands for the product `C_v × ∏_{j>1} C^(j)`, a compact open subgroup
of `∏_j (𝒟_j)ˣ = (ℚ_p ⊗_{𝒦₀} 𝒟)ˣ`, which this module keeps undecomposed
(the decomposition over the places `v^(j)` is not formalized, as recorded in
`HarrisSplitPrimePoints`). The level `K_p = C × ℤ_pˣ` is the inverse image of
`C × ℤ_pˣ` under the identification (4.2).

## Inputs

- `HarrisSplitPrimePoints` (submitted with `ImaginaryQuadraticSplitPoints` and
  `CentralExchangeSplitting` in candidate
  `da0b2727-b785-4787-9b7e-37ce24a50276`): `imaginaryQuadraticAlgebra ι`,
  `SecondKindInvolution.isConjugationOn` and
  `SecondKindInvolution.splitPrimePoints`.
- `ImaginaryQuadraticSplitTopology`: `FactorUnits` and `pointsHomeomorph`.
- Published: `CompactOpenLevel` (`Langlands.Shimura.Levels`), `prod`
  (`PartialLevelTower`), `transport` (`PEL.TraceSimilitudesLevels`),
  `awayOver` (`SplitLevelTower`), the point groups `σ.Points S`,
  `FiniteAdelicPoints`, `finiteLocalMap` (`Unitary.Adelic`), `DividingPoints`,
  `PrimeToPoints`, `finiteAdelicPointsSplit`, `dividingLocalMap`,
  `dividingLocalMap_finiteAdelicPointsSplit`, `pointsContinuousEquiv`
  (`Unitary.PointsSplit`), `harrisUnitaryLevelTower` (`Unitary.HarrisLevels`),
  `harrisPrimeToLevelTower` and `harrisPrimeToTowerIso`
  (`Unitary.HarrisSplitTower`), `isCompact_adicCompletionIntegers`
  (`Global.IntegralFiniteAdeles`) and `existsUnique_finitePlace_natCast_mem`
  (`Global.PrimeToFiniteAdeles`).

## Declarations

All declarations are in namespace `Langlands.Shimura`.

### Integer units

- `integerUnitsLevel v`, for a finite place `v` of `ℚ`, is the compact open
  level `ℤ_vˣ` of `ℚ_vˣ`: the units `c` with `c` and `c⁻¹` in the completed
  integers `v.adicCompletionIntegers ℚ` (`mem_integerUnitsLevel`). It is open
  because the completed integers are open (`Valued.isOpen_valuationSubring`)
  and the value and inverse maps of units are continuous, and compact by
  Mathlib's `Submonoid.units_isCompact` and the published compactness of the
  completed integers.

### The unique place above a prime

In namespace `AlgebraInvolution`, for a prime `p` and an element `v` of
`{v : FinitePlace ℚ // (p : 𝓞 ℚ) ∈ v.asIdeal}`:

- `dividingPlaceUnique p hp v` is the `Unique` structure on this subtype with
  default `v`, by `existsUnique_finitePlace_natCast_mem`.
- `dividingCompletionEquiv p hp v` is the isomorphism of topological
  `ℚ`-algebras `Π_{w ∣ p} ℚ_w ≃A[ℚ] ℚ_v`, evaluation at `v`
  (`dividingCompletionEquiv_apply`), from Mathlib's `RingEquiv.piUnique` and
  `Homeomorph.piUnique`.
- `σ.dividingPrimePointsEquiv p hp v : σ.DividingPoints p ≃ₜ* σ.Points ℚ_v`,
  for `σ : AlgebraInvolution ℚ A` with `A` finite over `ℚ`, is
  `pointsContinuousEquiv` of this isomorphism. `dividingPrimePointsEquiv_apply`
  states, by `rfl`, that it is the published local projection
  `σ.dividingLocalMap p v`.

### The Harris setting

As in `HarrisSplitPrimePoints`: `E` is a totally real number field, `K` a
totally complex quadratic extension, `F` an imaginary quadratic field,
`A` a `K`-algebra with `E`- and `ℚ`-algebra structures and scalar towers,
`σ : SecondKindInvolution E K A`, `ι : F →+* K`, `v` a finite place of `ℚ`
and `u : F →+* ℚ_v`.

- `SplitPrimeUnits A ι v u` is `FactorUnits F A ℚ_v` for the `F`-algebra
  structures `imaginaryQuadraticAlgebra ι` on `A` and `u.toAlgebra` on `ℚ_v`:
  the group `(ℚ_v ⊗[F, u] A)ˣ` with the units topology of the `ℚ_v`-module
  topology. Its group and topology instances are those of `FactorUnits`.
- `σ.splitPrimeHomeomorph ι v u : σ.rationalInvolution.Points ℚ_v ≃ₜ*
  SplitPrimeUnits A ι v u × ℚ_vˣ` is `pointsHomeomorph` for these
  structures; `splitPrimeHomeomorph_apply` states, by `rfl`, that its
  underlying map is `σ.splitPrimePoints ι v u`.
- `σ.splitPrimeLevel ι v u C`, for `C : CompactOpenLevel (SplitPrimeUnits A ι v u)`,
  is Harris's `K_p = C × ℤ_vˣ`: the transport of `prod C (integerUnitsLevel v)`
  along the inverse of `splitPrimeHomeomorph`. By `mem_splitPrimeLevel`, a
  point `g` lies in it exactly when the first component of
  `splitPrimeHomeomorph g` (the image of its algebra unit in
  `ℚ_v ⊗[F, u] A`) lies in `C` and its multiplier lies in `ℤ_vˣ`.
  `splitPrimeLevel_mono`: it is monotone in `C`.

Now assume `A` finite over `ℚ`, `p` prime, `v` a place whose prime ideal
contains `p`, and `u : F →+* ℚ_v`.

- `σ.splitPrimeDividingLevel ι p hp v u C` is `K_p` as a level of
  `GG(Π_{w ∣ p} ℚ_w) = σ.rationalInvolution.DividingPoints p`, transported
  along `dividingPrimePointsEquiv`. `mem_splitPrimeDividingLevel`: `g` lies in
  it exactly when `dividingLocalMap p v g` lies in `K_p`.
- `σ.splitPrimeAdelicLevel ι p hp v u C K'`, for a level `K'` of
  `GG(A_f^p) = σ.rationalInvolution.PrimeToPoints p`, is the level
  `K_p × K'` of `GG(A_f)`: the transport of
  `prod (splitPrimeDividingLevel …) K'` along the inverse of the published
  splitting `finiteAdelicPointsSplit p`. `mem_splitPrimeAdelicLevel`: a finite
  adelic point `g` lies in it exactly when its local image
  `finiteLocalMap v g` lies in `K_p` and its prime-to-`p` component lies in
  `K'`.

### The tower away from `p`

For `D : CentralSimpleUnitaryData E K A n` (with `ℚ → K → A` a scalar tower
and `A` finite over `ℚ`), the Harris signature hypothesis `h`, `ιF : F →+* K`,
`τ₀ : F →+* ℂ`, `p`, `v`, `u` and `C` as above:

- `harrisSplitPrimeTower D h ιF τ₀ p hp v u C` is the published
  `harrisPrimeToLevelTower D h ιF τ₀ p K₀` for
  `K₀ = D.toSecondKindInvolution.splitPrimeDividingLevel ιF p hp v u C`: the
  tower, over the levels `K'` of `GG(A_f^p)`, of the level spaces
  `GG(ℚ) \ ((X × GG(Π_{w ∣ p} ℚ_w) ⧸ K_p) × GG(A_f^p)) / K'` for the
  CM-compatible Harris domain `X`.
- `awayOver_splitPrime_obj`: the published away functor `awayOver` of the
  splitting at `K₀` sends `K'` to `splitPrimeAdelicLevel … C K'` (by `rfl`).
- `harrisSplitPrimeTowerIso` is the published `harrisPrimeToTowerIso` at
  `K₀`: the natural isomorphism from the Harris tower
  `harrisUnitaryLevelTower D h ιF τ₀` at the levels `K_p × K'` to
  `harrisSplitPrimeTower`.

## Scope

The level `C` is arbitrary; no principal congruence subgroup `C_v^{N,0}` of
Harris (1998), (A.2), and no maximal order of the local algebras, is
constructed. The decomposition of `(ℚ_p ⊗_{F, u} A)ˣ` over the places of `K`
above `u`, the condition of Harris that `C^(j)` is fixed while `C_v` varies,
the groups `GJ` and `GG` as distinct inner forms and their comparison away
from `v`, the rigid-analytic uniformization (4.3) and the spectral sequence of
Proposition 4.4 are not treated. The modules work for every place `v` and
embedding `u`; that `u` comes from Harris's fixed complex embedding of `𝒦₀`
and an identification of `ℂ` with an algebraic closure of `ℚ_p` is not
formalized.

## Provenance

Derived from Harris (1999), equations (4.1) and (4.2) and the definition of
`K(N, m)` on printed p. 309, and Harris (1998), Appendix, (A.1) and (A.2) on
printed p. 206, both read in the original. The undecomposed form `C × ℤ_pˣ`,
the transport through the published splittings and the identification of the
places above a prime are implementation choices. `harrisSplitPrimeTower` and
`harrisSplitPrimeTowerIso` are instances of the published
`HarrisSplitTower` declarations.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Formal dependencies: the modules listed under Inputs and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`Submonoid.units`, `Submonoid.units_isCompact`, `Valued.isOpen_valuationSubring`,
`RingEquiv.piUnique`, `RingEquiv.toRatAlgEquiv` and `Homeomorph.piUnique`.
