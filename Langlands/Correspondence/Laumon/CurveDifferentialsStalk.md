# Stalks of the differentials of a finite separable morphism of curves

Module `Langlands.Correspondence.Laumon.CurveDifferentialsStalk`, namespace
`Langlands.Henniart.Laumon`. It imports `Langlands.Correspondence.Laumon.CurveSemilocalRing` and
`Langlands.Correspondence.Laumon.TameCurveDifferent` (the semilocal ring
`B = curveSemilocalRing f y`, its prime `𝔓_y = curvePrime f y`, and the identification
`curveDifferentExponent_eq_count` of `curveDifferentExponent f y` with the exponent of `𝔓_y` in
`differentIdeal 𝒪_{X,f(y)} B`), the commutative-algebra modules
`Langlands.CommutativeAlgebra.KaehlerDifferent` and
`Langlands.CommutativeAlgebra.KaehlerMapBaseChange`, and
`WeilConjectures.AlgebraicGeometry.SmoothUniformizer`.

Let `κ` be a field, `X`, `Y` integral schemes over `Spec κ` with `X` smooth of relative
dimension one, and `f : Y ⟶ X` a morphism mapping the generic point to the generic point with
`κ(Y)/κ(X)` separable (hypotheses `hgen`, `hsep`). The module proves the local statements 1 and 3
of `CurveDifferentialsDifferentStatement` (statement 3, the length at a closed point, is the curve
case of Serre's characterization of the different by relative differentials, *Local Fields*,
III §7, Prop. 14, p. 59) about the map `𝒪_{Y,y} ⊗_{𝒪_{X,f(y)}} Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}`
(`KaehlerDifferential.mapBaseChange`), with the algebra structures fixed in
`IsStalkDifferentialsMapInjective` and `stalkDifferentialsCokernelLength`.

| Declaration | Statement |
|---|---|
| `formallySmooth_stalk κ x` | for `X` smooth over `κ`, `𝒪_{X,x}` (with `stalkAlgebraOver κ X x`) is a formally smooth `κ`-algebra |
| `formallyEtale_stalk_functionField f hgen hsep y` | `κ(Y)` is a formally étale `𝒪_{X,f(y)}`-algebra |
| `isStalkDifferentialsMapInjective_of_isSeparable κ f hgen hsep y` | `IsStalkDifferentialsMapInjective κ f y`, at every point `y` |
| `isScalarTower_curveSemilocalRingToStalk κ f y` | the inclusion `B ⊆ 𝒪_{Y,y}` is compatible with the `𝒪_{X,f(y)}`-algebra structures |
| `stalkDifferentialsCokernelLength_eq κ f hgen hsep y hy` | for `κ` perfect, `Y` smooth of relative dimension one and locally noetherian, `f` finite and `y` closed: `stalkDifferentialsCokernelLength κ f y = curveDifferentExponent f y` |

## Proofs

`formallySmooth_stalk`: the smooth locus of a smooth morphism is everything
(`Scheme.Hom.smoothLocus_eq_top`), and the weil-conjectures criterion
`Scheme.Hom.mem_smoothLocus_iff_formallySmooth` turns membership into formal smoothness of the
local ring.

`formallyEtale_stalk_functionField`: `κ(X)` is a localization of `𝒪_{X,f(y)}`, hence formally
étale over it, and `κ(Y)/κ(X)` is an algebraic separable field extension, hence formally étale
(`Algebra.FormallyEtale.of_isSeparable`); compose (the tower is
`isScalarTower_functionField`). The finiteness of `f` is not used here; it enters only in the
closed-point length `stalkDifferentialsCokernelLength_eq`.

`isStalkDifferentialsMapInjective_of_isSeparable`: with `A = 𝒪_{X,f(y)}` and `L = κ(Y)`,
`Ω_{A/κ}` is projective over `A` because `A` is formally smooth over `κ`
(`Algebra.FormallySmooth.projective_kaehlerDifferential`), hence flat; `L`
is formally étale over `A`; and `𝒪_{Y,y} → L` is injective. These are the hypotheses of
`KaehlerMapBaseChange.mapBaseChange_injective`: tensoring with `L` embeds
`𝒪_{Y,y} ⊗ Ω_{A/κ}` into `L ⊗ Ω_{A/κ} ≅ Ω_{L/κ}`. The argument needs neither the rank-one
freeness of the modules of differentials nor that `y` is closed, and `f` need not be finite.

`stalkDifferentialsCokernelLength_eq`: by `KaehlerMapBaseChange.length_quot_range_mapBaseChange`
the cokernel has the length of `Ω_{𝒪_{Y,y}/A}`. The Library supplies, for closed `y`, that `B` is
a Dedekind domain, finite and torsion-free over the discrete valuation ring `A`, with fraction
field separable over that of `A`, that `𝔓_y` is a maximal ideal over the maximal ideal of `A`
with separable residue extension (`isSeparable_residueField_curvePrime`, using that `κ` is
perfect), and that `𝒪_{Y,y}` is the localization of `B` at `𝔓_y` (`isLocalization_curvePrime`).
Then `KaehlerDifferent.length_kaehler_eq_count` (Serre III §7, Prop. 14 localized at `𝔓_y`) gives
the length of `Ω_{𝒪_{Y,y}/A}` as the exponent of `𝔓_y` in `differentIdeal A B`, which is
`curveDifferentExponent f y` by `curveDifferentExponent_eq_count`.
