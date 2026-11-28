# Differentials and the different of a finite separable morphism of curves

Module `Langlands.Correspondence.Laumon.CurveDifferentialsDifferent`, namespace
`Langlands.Henniart.Laumon`. It imports `Langlands.Correspondence.Laumon.CurveDifferentialsStalk`
(the stalk statements, and through it the statement module
`Langlands.Correspondence.Laumon.CurveRiemannHurwitz`), `Langlands.AlgebraicGeometry.StalkKaehler`
(germs of differentials) and the weil-conjectures modules
`WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus` (the zero scheme of a morphism of invertible
modules), `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`,
`WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula` and
`WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf` (ideal sheaves `𝒪_C(-E)` of effective
divisors on a smooth curve).

The main theorem `curveDifferentialsDifferentStatement : CurveDifferentialsDifferentStatement`
proves, for a perfect field `κ` and a finite morphism `f : Y ⟶ X` over `κ` of smooth proper
geometrically connected integral curves, mapping the generic point to the generic point with
`κ(Y)/κ(X)` separable, the five assertions of `CurveDifferentialsDifferentStatement`: injectivity
of `𝒪_{Y,y} ⊗ Ω_{𝒪_{X,f(y)}/κ} → Ω_{𝒪_{Y,y}/κ}` at every point, finiteness of the set of points
where its cokernel has nonzero length, the length `δ_y = curveDifferentExponent f y` at closed
points, `curveDifferent f y = δ_y`, and `Ω¹_{Y/κ} ≅ f^*Ω¹_{X/κ} ⊗ 𝒪_Y(D_f)` with `𝒪_Y(D_f)` the
dual of `Scheme.Divisor.idealSheaf (curveDifferent f)`.

The local length at a closed point is the curve case of Serre's characterization of the
different by the module of relative differentials (*Local Fields*, III §7, Prop. 14, p. 59: for
the integral closure `B` of a Dedekind domain `A` in a finite separable extension with separable
residue field extensions, `Ω_{B/A}` is cyclic with annihilator the different), applied to the
semilocal ring of `Y` over the local ring of `X`. The global isomorphism is not part of Serre's
proposition: it is obtained here from the zero scheme of `f^*Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}`, whose ideal
sheaf is the ideal sheaf of the effective divisor `curveDifferent f` (compare Hartshorne,
*Algebraic Geometry*, IV §2, Props. 2.1–2.3, pp. 300–301).

## The morphism `f^*Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}`

Variables (section `Map`): a commutative ring `κ`, a scheme `X` with `gX : X ⟶ Spec κ`, and
`f : Y ⟶ X`; `Y` is over `Spec κ` through `f ≫ gX`.

| Declaration | Statement |
|---|---|
| `differentialsPushforwardHom gX f` | the morphism `Ω¹_{X/κ} ⟶ f_* Ω¹_{Y/κ}` given by the derivation `s ↦ d (f^♯ s)` (weil-conjectures `Scheme.Hom.pushforwardDerivation`) through the universal property `Scheme.Hom.relativeDifferentialsHomEquiv` |
| `differentialsPullbackHom gX f` | the morphism `f^* Ω¹_{X/κ} ⟶ Ω¹_{Y/κ}`, adjoint to it under `Scheme.Modules.pullbackPushforwardAdjunction f` |
| `differentialsPushforwardApp gX f V` | `differentialsPushforwardHom` on sections, `Γ(Ω¹_{X/κ}, V) →+ Γ(Ω¹_{Y/κ}, f⁻¹ V)` |
| `differentialsPushforwardApp_sectionsD` | it sends `d a` to `d (f^♯ a)` |
| `differentialsPushforwardApp_smul` | it sends `a • s` to `f^♯ a • (image of s)` |
| `differentialsPullbackHom_app_unit` | `differentialsPullbackHom` sends the pullback `η s` (the unit of the adjunction) of a section `s` over `V` to the image of `s` in `Γ(Ω¹_{Y/κ}, f⁻¹ V)` |

## Comparison with the local rings

Variables (section `Stalk`): `κ`-algebra structures on `𝒪_{X,f(y)}` and `𝒪_{Y,y}` and an
`𝒪_{X,f(y)}`-algebra structure on `𝒪_{Y,y}`, forming a scalar tower, such that the algebra map
`𝒪_{X,f(y)} → 𝒪_{Y,y}` is the stalk map of `f` (`hAO`) and the `κ`-structures are the germs of
the structure maps of `gX` and `f ≫ gX` (`hκX`, `hκY`, as in
`Langlands.AlgebraicGeometry.StalkKaehler`).

| Declaration | Statement |
|---|---|
| `toStalk_differentialsPushforwardHom` | for affine opens `V ∋ f y` and `f⁻¹ V`, `StalkKaehler.toStalk` of `differentialsPushforwardApp s` is `KaehlerDifferential.map κ κ 𝒪_{X,f(y)} 𝒪_{Y,y}` of `StalkKaehler.toStalk s` |
| `germ_comp_specStructureMap_eq_stalkAlgebraOver κ z U hz` | for `Z` over `Spec κ`, the algebra structure `stalkAlgebraOver κ Z z` is the germ of the structure map on every open `U ∋ z` |
| `germ_comp_specStructureMap_comp κ f y U hy` | the structure map of `Y` through `f`, followed by the germ at `y`, is `stalkAlgebraOver κ X (f y)` followed by the stalk map of `f` |

The last two lemmas say that the algebra structures of `IsStalkDifferentialsMapInjective` and
`stalkDifferentialsCokernelLength` satisfy `hκX` and `hκY`.

## The zero scheme at a closed point

Variables (section `ClosedPoint`): a field `κ`, integral schemes `X`, `Y` over `Spec κ`, smooth of
relative dimension one, `Y` locally noetherian, `f : Y ⟶ X` finite over `Spec κ` with `hgen` and
`hsep` as above.

| Declaration | Statement |
|---|---|
| `ordAt_zeroLocus_differentialsPullbackHom κ f hgen hsep y hy` | for `κ` perfect and `y` closed: the order at `y` (`Scheme.IdealSheafData.ordAt`) of the zero scheme `Scheme.Modules.Hom.zeroLocus` of `differentialsPullbackHom` is `curveDifferentExponent f y`, and `differentialsPullbackHom ≠ 0` |

## Proofs

`differentialsPullbackHom_app_unit`: by `Adjunction.homEquiv_unit`, the adjoint of
`differentialsPullbackHom` is the unit followed by its pushforward, which is
`differentialsPushforwardHom`.

`toStalk_differentialsPushforwardHom`: by induction on the span of the `D a` in
`Ω[Γ(X, V)⁄κ]`; on `D a` both sides are `D` of the germ of `f^♯ a`
(`differentialsPushforwardApp_sectionsD`, `StalkKaehler.toStalk_sectionsD`,
`KaehlerDifferential.map_D`, `Scheme.Hom.germ_stalkMap_apply`); sums and scalar multiples by
additivity and `differentialsPushforwardApp_smul`, `StalkKaehler.toStalk_smul`.

`ordAt_zeroLocus_differentialsPullbackHom`: `Ω¹_{X/κ}` and `Ω¹_{Y/κ}` are invertible
(`Scheme.Hom.isInvertible_relativeDifferentials`, smoothness of relative dimension one), and so is
`f^*Ω¹_{X/κ}`. Choose an affine open `V ∋ f y` with a free generator `eX` of `Ω¹_{X/κ}` on `V`;
its pullback `η eX` is a free generator of `f^*Ω¹_{X/κ}` on `f⁻¹ V`
(`Scheme.Modules.IsFreeGenerator.pullback_unit_app`). Choose an affine open `U' ∋ y` inside
`f⁻¹ V` with a free generator `eN` of `Ω¹_{Y/κ}` on `U'`, and write the image of `η eX` (restricted
to `U'`) as `b • eN`. By `Scheme.Modules.Hom.ideal_zeroLocus` the zero scheme is `(b)` on `U'`,
so its order at `y` is the order of the germ of `b` in the discrete valuation ring `𝒪_{Y,y}`
(`Scheme.IdealSheafData.ordAt_eq`, `Scheme.ord_algebraMap_stalk`). On the local side,
`StalkKaehler.exists_linearEquiv_of_isFreeGenerator` gives `e : 𝒪_{Y,y} ≅ Ω[𝒪_{Y,y}⁄κ]` with
`e 1` the germ of `eN`, `StalkKaehler.span_toStalk_eq_top` says the germ `ω` of `eX` spans
`Ω[𝒪_{X,f(y)}⁄κ]`, and `differentialsPullbackHom_app_unit`, `StalkKaehler.toStalk_map` and
`toStalk_differentialsPushforwardHom` give `map(ω) = germ(b) • e 1`. Hence
`KaehlerMapBaseChange.length_quot_range_mapBaseChange_eq_ord` computes the cokernel length as
`Ring.ord 𝒪_{Y,y} (germ b)`, while `stalkDifferentialsCokernelLength_eq` computes it as
`curveDifferentExponent f y`. Since this length is finite, the germ of `b` is nonzero, which gives
both the order and `differentialsPullbackHom ≠ 0` (otherwise `b • eN = 0` and `b = 0`).

`curveDifferentialsDifferentStatement`: `Y` is locally noetherian (of finite type over `κ`) and
quasi-compact (proper over `Spec κ`), hence noetherian, and it has a closed point `y₀`. By
`ordAt_zeroLocus_differentialsPullbackHom` at `y₀`, `φ = differentialsPullbackHom` is nonzero, so
its zero scheme is invertible (`Scheme.Modules.Hom.isInvertible_zeroLocus`) and equals
`Scheme.Divisor.idealSheaf E` for some effective divisor `E`
(`Scheme.IdealSheafData.IsInvertible.exists_eq_idealSheaf`). At every closed point `P`,
`Scheme.Divisor.ordAt_idealSheaf` and `ordAt_zeroLocus_differentialsPullbackHom` give
`E P = curveDifferentExponent f P`; so the function `P ↦ δ_P` has finite support, and by the
definition of `curveDifferent`, `curveDifferent f = E`. Then:

1. injectivity is `isStalkDifferentialsMapInjective_of_isSeparable`;
2. a point `y` with nonzero cokernel length is either closed, and then
   `δ_y = E ⟨y, _⟩ ≠ 0` by statement 3, so `y` lies in the image of the finite support of `E`; or
   not closed, and then its coheight is at most one
   (`Scheme.coheight_le_one_of_smoothOfRelativeDimension_one`) and not one
   (`Scheme.isClosed_of_coheight_eq_one`), so zero, and `y` is the generic point
   (`Scheme.eq_genericPoint_of_coheight_eq_zero`);
3. the cokernel length at closed points is `stalkDifferentialsCokernelLength_eq`;
4. `curveDifferent f P = E P = δ_P`;
5. `Scheme.Modules.Hom.nonempty_iso_dual_toModules_tensorObj φ` gives
   `Ω¹_{Y/κ} ≅ (zero scheme of φ)ᵛ ⊗ f^*Ω¹_{X/κ}`, where `Ω¹_{Y/κ}` is that of `f ≫ (X ↘ Spec κ)`,
   equal to `Y ↘ Spec κ` because `f` is over `Spec κ` (`comp_over`); the zero scheme is
   `idealSheaf E = idealSheaf (curveDifferent f)`, and the braiding `β_` swaps the factors.
