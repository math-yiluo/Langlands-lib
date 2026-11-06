# Reduction of rational strongly regular representatives to two prerequisites

Author: Worker 1601.

This module proves the target
`Langlands.GroupScheme.QuasiSplitSimplyConnectedRegularConjugateStatement.{u}`
conditionally. Two prerequisite statements are explicit hypotheses:

- `QuasiSplitRegularClassRationalStatement.{u}`
  (`Rational/QuasiSplitRegularClassRationalStatement.lean`). A Galois-stable
  strongly regular class in a simply connected quasi-split group contains a
  rational point (Borel–Springer 8.6).
- `RegularConjugateFiniteGaloisStatement.{u}`
  (`Rational/RegularConjugateFiniteGaloisStatement.lean`). If a rational point
  `x` is geometrically conjugate to a strongly regular point `z` over `L`,
  then the centralizer of `x` lies in a closed `K`-torus, and the conjugacy
  holds over a finite Galois extension.

Neither hypothesis is proved here. The closing theorem of the target task
combines this reduction with their published proofs.

## Declarations

All declarations are in namespace
`Langlands.GroupScheme.QuasiSplitRegularConjugate`, except the final theorem,
which is in `Langlands.GroupScheme`. Throughout, `b : Spec L ⟶ Spec K` is
induced by `algebraMap K L` and `U = Over.mk b`.

- `baseChangePointsEquiv_toUnit_comp`. For `z : Over.mk b ⟶ G.X` and a test
  `Z` over `Spec L`, the base-change point equivalence sends the restriction
  to `Z` of the `L`-rational point `(baseChangeBasePointsEquiv b G).symm z` of
  `G_L` to `baseChangeTestPoint Z ≫ z`. The proof compares underlying
  morphisms with `baseChangeBasePointsEquiv_left`.
- `coverPoint e y := (e.toFun (𝟙 U)).symm (toUnit U ≫ y)`. This is the point
  of `G` over `U` that `e` at the identity point of the cover carries to `y`.
- `toFun_comp_coverPoint`. For every point `w : Z ⟶ U`,
  `e.toFun w (w ≫ coverPoint e y) = toUnit Z ≫ y`. It follows from the
  naturality of `e` at `(w, 𝟙 U)`.
- `centralizer_coverPoint`. Every point `c` of `G_L` on a test `Z` over
  `Spec L` that commutes with the restricted `L`-point of `coverPoint e y`
  factors through `(baseChange b).map j ≫ e.toBaseChangeIso.inv`. Proof:
  - Push the commutation to `G` over `(Over.map b).obj Z` with
    `baseChangePointsEquiv`, then apply `e` at `baseChangeTestPoint Z`.
  - By `toFun_comp_coverPoint` and `toBaseChangeIso_hom_points`, the point
    `c ≫ e.toBaseChangeIso.hom` of `H_L` corresponds to a point of `H`
    commuting with `y`.
  - The hypothesis on `y` factors that point through `S`. Its adjoint
    `(baseChangePointsEquiv b S Z).symm s` is the required factor, by
    `baseChangePointsEquiv_comp` and `Iso.hom_inv_id`.
- `algebraicClosureCoverPoint K L`. The morphism of covers
  `Spec (AlgebraicClosure L) ⟶ Spec L` over `K`, induced by `algebraMap`. The
  scalar tower identifies the composite with the structure map.
- `coverPoint_galoisStable`. For every endomorphism `σ` of `U`, some point `h`
  of `G` over the algebraic closure of `L` satisfies
  `h * (q ≫ coverPoint e y) * h⁻¹ = q ≫ σ ≫ coverPoint e y`, where
  `q = algebraicClosureCoverPoint K L`. Proof:
  - `HasDiscrepancy` at the points `(𝟙 U, σ)` and `toFun_comp_coverPoint`
    give `a.act (ξ (𝟙 U) σ) (σ ≫ z) = z` for `z = coverPoint e y`, by
    injectivity of `e.toFun (𝟙 U)`.
  - The central isogeny `π` is surjective and locally of finite
    presentation. So `exists_point_lift_of_locallyOfFiniteType_surjective`
    lifts the algebraically closed point `q ≫ ξ (𝟙 U) σ` of `A` to a point
    `h₀` of `G`.
  - Naturality of the action and the innerness hypothesis on `a` give
    `q ≫ z = h₀ * (q ≫ σ ≫ z) * h₀⁻¹`. The witness is `h = h₀⁻¹`.
- `quasiSplitSimplyConnectedRegularConjugate_of_classRational`. The
  conditional theorem, proved as follows.
  - The torus `S_L = (baseChange b).obj S` is a torus by `IsTorus.baseChange`.
  - The inclusion `(baseChange b).map j ≫ e.toBaseChangeIso.inv` is closed, by
    `IsClosedSubgroup.baseChange`, `IsClosedSubgroup.of_iso` and
    `IsClosedSubgroup.comp`.
  - With `centralizer_coverPoint` and `coverPoint_galoisStable`, the first
    hypothesis yields a rational `x` conjugate to `coverPoint e y` over a
    field.
  - The second hypothesis, with `IsQuasiSplit.isConnectedReductive`, yields
    the closed torus `T`, a finite Galois `L'`, a morphism of covers `r` and a
    point `g'` with `g' x g'⁻¹ = r ≫ coverPoint e y`.
  - Finally `toFun_comp_coverPoint` at `r` gives
    `e.toFun r (g' x g'⁻¹) = toUnit _ ≫ y`.

## Provenance

Provenance: internal. This is the argument of Steinberg (1965), §10 (printed
p.78, PDF p.31), source `steinberg-1965-regular-elements-semisimple-groups`.
In the twisted group the Galois action is corrected by inner automorphisms,
so the class of the point corresponding to `y` is stable, and Theorem 1.7
supplies the rational `x`. Here that argument is carried out on the finite
cover, with the cocycle values lifted along the central isogeny `π` over an
algebraic closure, following Kneser's remark in §11 (printed p.79, PDF p.32).
The rational-point and descent inputs are the two explicit hypotheses.

## Scope

- Arbitrary universe `u` and arbitrary fields `K`, with no perfectness,
  infinitude or splitness hypothesis.
- The two prerequisite statements remain explicit hypotheses.
