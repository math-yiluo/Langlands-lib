# Rational points of algebraic spaces over a field lift to affine étale charts

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.RationalPointEtaleLiftStatement.{u}`
(Knutson, *Algebraic Spaces*, II.6.4; Stacks Project, Tag 0BBP, the rational-point case).
Let `k` be a field and `X` an algebraic space over `Spec k`. Every `k`-point `x` of `X` is
the image, under `RingPoints.map f`, of a `k`-point `u` of an affine scheme `U` over
`Spec k`, where `f : U → X` is étale.

The statement assumes that `X` is quasi-separated. The proof does not use this hypothesis.
The Lean proof does not follow the cited sources. It takes its own route: a Galois-descent
argument in the style of Weil restriction, whose last step is the Galois descent of a
`K`-point. All names below are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace` unless qualified otherwise.

## Statements

- `RationalPointEtaleLiftProof.exists_invariant_chart_point`: let `X` be an algebraic space
  over `Spec k` and let `x̂ : h_{Spec k} ⟶ X.presheaf`. Let `K/k` be a finite Galois
  extension, `V` a scheme over `Spec k` with `V.hom` separated, and `a : h_V ⟶ X.presheaf`
  étale. Let `v : specOver k K ⟶ V` and `π : specOver k K ⟶ ringTest k k` satisfy
  `h(v) ≫ a = h(π) ≫ x̂`. Then there are `M` over `Spec k` with `M.left` affine, an étale
  `tM : h_M ⟶ X.presheaf`, and `w : specOver k K ⟶ M` with
  `specOverMap g.toAlgHom ≫ w = w` for every `g : K ≃ₐ[k] K` and
  `h(w) ≫ tM = h(π) ≫ x̂`.
- `RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement :
  RationalPointEtaleLiftStatement.{u}`, the target.

## Proof of `exists_invariant_chart_point`

Write `G = K ≃ₐ[k] K`, a finite group.

1. `ChartFibrePower.exists_of_finite` gives the `G`-fold fibre power `Y` of `a`. It is
   separated over `Spec k` and has étale projections `Y.pr e`. `G` acts on `Y` by
   `Y.act g`, with `Y.act g ≫ Y.pr e = Y.pr (g * e)`; this is the `OverAction` `ρ`.
2. `σ = OverAction.galoisAction` is the action of `G` on `Spec K`. It is free
   (`galoisAction_isFree`). The diagonal action `τ = ρ.prod σ` on
   `Z = prodOver Y (specOver k K)` is therefore free (`prod_isFree`). `Z` is separated over
   `Spec k`, hence separated as a scheme, because `Spec k` is affine.
3. Every morphism `specOver k K ⟶ ringTest k k` is the same morphism
   (`GaloisChartPoint.ringTest_self_hom_ext`), so `specOverMap g.toAlgHom ≫ π = π`. Hence
   the family `e ↦ specOverMap e.toAlgHom ≫ v` has a common image `h(π) ≫ x̂` in `X`. It
   therefore defines a point `y₀ : specOver k K ⟶ Y`. Let
   `z = prodLift y₀ (𝟙 _) : specOver k K ⟶ Z`.
4. `z` is equivariant: `z ≫ τ.act g = σ.act g ≫ z`. On the second factor both sides are
   `σ.act g`. On the first factor, after projecting with `Y.pr e`, the left side is
   `specOverMap (g * e) ≫ v` and the right side is
   `specOverMap g ≫ specOverMap e ≫ v`. These agree by the action law `σ.mul`.
5. The map `t = h(prodFst) ≫ h(Y.pr 1) ≫ a : h_Z ⟶ X.presheaf` is étale. Here `prodFst` is
   étale because `Spec K → Spec k` is étale, and the other two maps are étale by step 1;
   `IsEtale.comp` and `isEtale_map` combine them. `t` is invariant under `τ`: by
   `prod_act_fst` and `Y.act_pr`, `h(τ.act g) ≫ t = h(prodFst) ≫ h(Y.pr g) ≫ a`, and all
   projections have the same image in `X` (`Y.w`).
6. `OverAction.exists_affine_chart_of_point` applied to `τ`, `σ`, `t` and `z` gives `M`,
   `tM` and `w` with `M.left` affine, `tM` étale, `w` invariant, and
   `h(w) ≫ tM = h(z) ≫ t`. The right side equals `h(y₀ ≫ Y.pr 1) ≫ a = h(π) ≫ x̂` by
   step 3.

## Proof of the target

Let `x` be a `k`-point of `X`, and let `x̂ = uliftYonedaEquiv.symm x`.

1. `GaloisChartPoint.exists_galois_chart` gives a finite Galois extension `K/k`, an affine
   `V` separated over `Spec k`, an étale `a : h_V ⟶ X.presheaf` and a `K`-point `v` with
   `h(v) ≫ a = h(specOverMap (Algebra.ofId k K)) ≫ x̂`.
2. `exists_invariant_chart_point`, with `π = specOverMap (Algebra.ofId k K)`, gives the
   affine `M`, the étale `tM` and the invariant `K`-point `w`.
3. `GaloisChartPoint.exists_desc_of_galois_invariant` descends `w` to a `k`-point
   `u : ringTest k k ⟶ M` with `specOverMap (Algebra.ofId k K) ≫ u = w`.
4. Take `U = M`, `f = AlgebraicSpace.homMk tM`, and the point `u`. `M.left` is affine and
   `hom f = tM` is étale. It remains to show that
   `RingPoints.map f ((schemeRingPointsEquiv k M k).symm u) = x`. By
   `GaloisChartPoint.changeRing_injective`, it suffices to check this after base change to
   `K`. Through `uliftYonedaEquiv`, the left side corresponds to `h(u) ≫ tM` and `x`
   corresponds to `x̂`. After precomposition with `Spec K → Spec k`, the two become
   `h(w) ≫ tM` and `h(specOverMap (Algebra.ofId k K)) ≫ x̂`
   (`uliftYonedaEquiv_naturality`). These are equal by step 2.

## Modules

The proof uses the helper modules `GaloisChartPoint` (Galois `K`-points of étale charts,
Galois descent of invariant points, injectivity of base change on points),
`ChartFibrePower` (fibre powers of a chart and the permutation action),
`FiniteActionChartDescent` (descent along quotients by finite free actions) and
`OverActionQuotientChart` (stable affine neighbourhoods, quotients, and the Galois action on
`Spec K`). These modules are in the same directory.
