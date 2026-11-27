# The semilocal ring of a finite morphism of curves and the local different exponent

Module `Langlands.Correspondence.Laumon.CurveSemilocalRing`, namespace
`Langlands.Henniart.Laumon`. It proves the facts about the semilocal ring `curveSemilocalRing`
and the local different exponent `curveDifferentExponent` of
`Langlands.Correspondence.Laumon.CurveRiemannHurwitz` that every use of the exponent needs: the
`if` in the definition of `curveDifferentExponent` takes its first branch, and at a closed point
`y` the exponent is the exponent of the prime `𝔓_y = B ∩ 𝔪_y` in Mathlib's different ideal, at
which the local ring `𝒪_{Y,y}` is the localization of `B` and the ramification index of the
morphism is Mathlib's ramification index.

The module imports `Langlands.MathlibBase` (never `Mathlib` whole),
`Langlands.Correspondence.Laumon.CurveRiemannHurwitz`,
`Langlands.CommutativeAlgebra.IntegralClosureDvrCenter`,
`Langlands.CommutativeAlgebra.TameDifferent` and the modules
`WeilConjectures.AlgebraicGeometry.Curve.SerreDuality`,
`WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf`,
`WeilConjectures.AlgebraicGeometry.NormalizationCover` and
`WeilConjectures.Mathlib.AlgebraicGeometry.OrderOfVanishing` of weil-conjectures.

## Setting

Throughout, `κ` is a field, `X` and `Y` are integral schemes over `Spec κ`, `X` with
`[SmoothOfRelativeDimension 1 (X ↘ Spec (.of κ))]`, and `f : Y ⟶ X` is a morphism with
`[IsFinite f]`, `hgen : f (genericPoint Y) = genericPoint X` and

```lean
hsep : letI := (f.functionFieldMap hgen).hom.toAlgebra
  Algebra.IsSeparable X.functionField Y.functionField
```

The results at closed points also assume `[SmoothOfRelativeDimension 1 (Y ↘ Spec (.of κ))]`,
and those about `curveDifferentExponent` and the ramification index `[IsLocallyNoetherian Y]`.
These are the hypotheses of `TameCurveDifferentStatement` and its two companions, without
properness, geometric connectedness, `f.IsOver` and perfectness of `κ`, which the results do not
use. For a point `y` of `Y`, the maps `A = 𝒪_{X,f(y)} → 𝒪_{Y,y} → κ(Y)` make `κ(Y)` an
`A`-algebra (`curveStalkFunctionFieldAlgebra`). Write
`B = curveSemilocalRing f y = integralClosure A κ(Y)`.
In the statements below the instances `IsDedekindDomain B` and `Module.IsTorsionFree A B` that
`differentIdeal A B` needs are supplied, by `haveI` in the statement, by the first two results.

## Definitions

| Declaration | Content |
|---|---|
| `curveStalkAlgebra f y` | the stalk map `𝒪_{X,f(y)} → 𝒪_{Y,y}` as an algebra structure (`abbrev`), with `isLocalHom_curveStalkAlgebra` and `isScalarTower_curveStalkAlgebra` (the tower `𝒪_{X,f(y)} → 𝒪_{Y,y} → κ(Y)`) |
| `curvePrime f y : Ideal (curveSemilocalRing f y)` | the ideal `𝔓_y = B ∩ 𝔪_y`: `centerIdeal 𝒪_{X,f(y)} 𝒪_{Y,y} κ(Y)` of `Langlands.CommutativeAlgebra.IntegralClosureDvrCenter`, spanned by the elements of `B` that are images of elements of the maximal ideal of `𝒪_{Y,y}` |
| `curveSemilocalRingToStalk f y` | for `𝒪_{Y,y}` integrally closed, the inclusion `B → 𝒪_{Y,y}` of subrings of `κ(Y)`; `algebraMap_curveSemilocalRingToStalk` says that it commutes with the inclusions in `κ(Y)` |

## At every point

| Declaration | Statement |
|---|---|
| `isDedekindDomain_stalk κ x` | for `X` smooth of relative dimension one over `κ` and integral, every local ring `𝒪_{X,x}` is a Dedekind domain |
| `isDiscreteValuationRing_stalk κ hx` | for `x` closed, `𝒪_{X,x}` is a discrete valuation ring |
| `stalkSpecializes_functionFieldMap`, `functionFieldMap_algebraMap` | `𝒪_{X,f(y)} → κ(X) → κ(Y)` (through `f.functionFieldMap hgen`) equals `𝒪_{X,f(y)} → 𝒪_{Y,y} → κ(Y)` |
| `isScalarTower_functionField` | hence `IsScalarTower 𝒪_{X,f(y)} κ(X) κ(Y)` for the algebra structure `(f.functionFieldMap hgen).hom.toAlgebra` |
| `algebraMap_stalk_functionField_injective` | `𝒪_{X,f(y)} → κ(Y)` is injective |
| `isTorsionFree_curveSemilocalRing` | `Module.IsTorsionFree 𝒪_{X,f(y)} (curveSemilocalRing f y)` |
| `isAlgebraic_stalk_functionField` | `κ(Y)` is algebraic over `𝒪_{X,f(y)}` |
| `isDedekindDomain_curveSemilocalRing` | `IsDedekindDomain (curveSemilocalRing f y)` |
| `finite_curveSemilocalRing` | `Module.Finite 𝒪_{X,f(y)} (curveSemilocalRing f y)` |
| `isSeparable_fractionRing_curveSemilocalRing` | `Algebra.IsSeparable (FractionRing 𝒪_{X,f(y)}) (FractionRing (curveSemilocalRing f y))`, for `FractionRing.liftAlgebra` |
| `curveDifferentExponent_eq` | `curveDifferentExponent f y` is the first branch of its definition: the `toNat` of the least `Y.ord d y` over the nonzero `d` of `differentIdeal A B` |

So at every point `y` the ring `B` is a Dedekind domain, torsion-free and finite over `A`, and
`curveDifferentExponent` is given by the first branch of its `if`. The fraction field of `A` is
`κ(X)` (Mathlib's instance `IsFractionRing (X.presheaf.stalk x) X.functionField`), and `κ(Y)` is
finite (`AlgebraicGeometry.Scheme.Hom.finiteDimensional_functionField` of weil-conjectures) and,
by `hsep`, separable over it, compatibly with `A` by `isScalarTower_functionField`.

## At a closed point

For `y` closed (`hy : IsClosed {y}`), with `Y` smooth of relative dimension one over `κ`:

| Declaration | Statement |
|---|---|
| `isDiscreteValuationRing_stalk_apply` | `𝒪_{X,f(y)}` is a discrete valuation ring |
| `maximalIdeal_stalk_apply_ne_bot` | its maximal ideal is nonzero |
| `curvePrime_liesOver` | `(curvePrime f y).LiesOver (maximalIdeal 𝒪_{X,f(y)})` (this holds at every point `y`) |
| `isMaximal_curvePrime` | `(curvePrime f y).IsMaximal` |
| `isLocalization_curvePrime` | for the algebra structure `(curveSemilocalRingToStalk f y).toAlgebra`, `IsLocalization.AtPrime 𝒪_{Y,y} (curvePrime f y)`: the localization of `B` at `𝔓_y` is `𝒪_{Y,y}`, as subrings of `κ(Y)` |
| `curveDifferentExponent_eq_count` | `curveDifferentExponent f y = (normalizedFactors (differentIdeal A B)).count (curvePrime f y)` |
| `ramificationIndex_eq_ramificationIdx` | `f.ramificationIndex y = ((curvePrime f y).ramificationIdx 𝒪_{X,f(y)} : ℤ)` |

The last two are the exponent of `𝔓_y` in Mathlib's different ideal (as a multiplicity in
`UniqueFactorizationMonoid.normalizedFactors`) and Mathlib's ramification index
`Ideal.ramificationIdx`, the forms used by `pow_sub_one_dvd_differentIdeal` and
`Langlands.CommutativeAlgebra.TameDifferent.count_normalizedFactors_differentIdeal`.

## Proofs

- **Dedekind stalks.** A local ring of a smooth curve is a valuation ring
  (`AlgebraicGeometry.Scheme.valuationRing_stalk` of weil-conjectures) and is Noetherian
  (`X` is locally Noetherian, being locally of finite type over `κ`); a Noetherian valuation ring
  is Bézout and Noetherian, hence a principal ideal domain, hence a Dedekind domain (Mathlib's
  instances). At a closed point it is a discrete valuation ring by
  `AlgebraicGeometry.Scheme.isDiscreteValuationRing_stalk_of_isClosed`, and `f(y)` is closed when
  `y` is (`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_apply`, `f` being finite).
- **The tower.** `f.functionFieldMap hgen` is the specialization map of `X` from `f(η_Y)` to `η_X`
  followed by the stalk map at `η_Y`; composing specialization maps
  (`TopCat.Presheaf.stalkSpecializes_comp`) and exchanging them with stalk maps
  (`AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap`) gives
  `stalkSpecializes_functionFieldMap`. Injectivity of `A → κ(Y)` follows from the tower, since
  `A → κ(X)` is injective (`IsFractionRing.injective`) and `κ(X) → κ(Y)` is a field map.
- **The semilocal ring.** `B` is a Dedekind domain by Mathlib's `integralClosure.isDedekindDomain`
  and finite over `A` by `IsIntegralClosure.finite`, both for the finite separable extension
  `κ(Y) / κ(X)` of the fraction field of the Dedekind domain `A`; torsion-freeness is the
  injectivity of `A → B` (`Module.isTorsionFree_iff_algebraMap_injective`), which follows from
  that of `A → κ(Y)`. `isSeparable_fractionRing_curveSemilocalRing` is
  `Langlands.CommutativeAlgebra.TameDifferent.isSeparable_fractionRing` with `K = κ(X)` and
  `L = κ(Y)`, the fraction field of `B` being `κ(Y)`
  (`integralClosure.isFractionRing_of_finite_extension`).
- **Closed points.** With `O = 𝒪_{Y,y}` a discrete valuation ring and `𝒪_{X,f(y)} → O` a local
  homomorphism, the results of `Langlands.CommutativeAlgebra.IntegralClosureDvrCenter` apply:
  `centerIdeal_isMaximal`, `centerIdeal_liesOver` and `isLocalization_atPrime`.
- **The exponent.** If the different ideal `D` is `⊥`, both sides of
  `curveDifferentExponent_eq_count` are `0` (the set of nonzero elements of `D` is empty and
  `sInf ∅ = 0` in `ℤ`; `normalizedFactors 0 = 0`). Otherwise, for `0 ≠ d ∈ B`, the order
  `Y.ord d y` is the `toNat` of the valuation of `d` in `O`: `y` has coheight one
  (`AlgebraicGeometry.Scheme.coheight_eq_one_of_isClosed`),
  `AlgebraicGeometry.Scheme.ord_algebraMap_stalk` identifies `Y.ord` with Mathlib's `Ring.ord`,
  and `Ring.ord_eq_addVal` with `IsDiscreteValuationRing.addVal`. By
  `isLeast_count_normalizedFactors` the exponent of `𝔓_y` in `D` is the least of these valuations,
  hence the infimum in the definition of `curveDifferentExponent`.
- **The ramification index.** `f.ramificationIndex y` is `Y.ord` at `y` of the image of a
  generator `t` of the maximal ideal of `A` chosen by `Classical.epsilon` (the definition of
  `AlgebraicGeometry.Scheme.Hom.ramificationIndex`); such a generator exists since `A` is a
  discrete valuation ring, and its image in `O` is nonzero. As above `Y.ord` of it is its valuation
  in `O`, which is the ramification index of `𝔓_y` by `ramificationIdx_centerIdeal`.
