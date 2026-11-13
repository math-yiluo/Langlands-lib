# Assembly of connected torus Iwahori models from focused inputs

Lean module: `Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly`.

Author: Worker 5282, for Task 6162 (`40cc6939-3c2a-4f23-b897-bccdd7b7ca80`).

This module reduces the published target
`UnramifiedTorusIwahoriModelStatement.{u}` to four focused propositions and
proves the reduction. It does not prove the target, and it proves none of the
four inputs.

## The assembly statement

`UnramifiedTorusIwahoriModelAssemblyStatement.{u}` is the implication

```text
IntegralModel.SmoothHomExtensionStatement.{u} →
UnramifiedTorusBoundedModelStatement.{u} →
UnramifiedTorusConnectedBoundStatement.{u} →
UnramifiedTorusIwahoriConnectedImageStatement.{u} →
UnramifiedTorusIwahoriModelStatement.{u}
```

The inputs are:

1. `IntegralModel.SmoothHomExtensionStatement` (published, module
   `Langlands.GroupScheme.IntegralModel.SmoothHomExtension`; proof task
   Task 6312). Over a Henselian discrete valuation ring with separably closed
   residue field, a generic homomorphism `f` extends from a smooth model `M`
   to an arbitrary model `N` when it carries `M.integralPoints` into
   `N.integralPoints`. This is KP Corollary 2.10.10 with Remark 2.10.19.
2. `UnramifiedTorusBoundedModelStatement` (new, paired module of that name).
   Every torus over `K = inertiaFixedField F` has a smooth model over
   `O = fixedFieldIntegers F` whose integral points are exactly
   `characterValuationKernel (fixedFieldValuation F) T.toGrp`, the maximal
   bounded subgroup `T(K)^1`. This is KP Proposition B.7.2(2).
3. `UnramifiedTorusConnectedBoundStatement` (new). For `T` split by a finite
   Galois `L`, every smooth model of `T` with geometrically connected fibres
   has integral points inside
   `torusNormIwahori K L (intermediateValuation F L) T`, that is `T(K)^0`.
   This is KP Corollary B.8.7 with the argument of Proposition B.8.8(3).
4. `UnramifiedTorusIwahoriConnectedImageStatement` (new). For the same `T`
   and `L`, `T(K)^0` is the image under some homomorphism `n : S ⟶ T.toGrp`
   of the integral points of a smooth model `W` of `S` with geometrically
   connected fibres. In the source, `W` is the Weil restriction of a split
   torus over the integers of `L`, and `n` is the norm (KP Lemma B.3.1 and
   Definition 2.5.13).

The three new inputs quantify over exactly the target's `F`, `T` and `L`;
the second needs only that `T` is a torus. Each paired Markdown gives the
exact source locations and scope.

## Source route

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Proposition B.8.4(3), printed pp. 681–682 / PDF pp. 712–713, takes `T^0` to
be the relative identity component of the smooth model `T^ft` of B.7.2.
Remark B.8.5, printed p. 682 / PDF p. 713, extends homomorphisms from smooth
models into `T^ft` and factors them through `T^0` when the source has
connected fibres. Corollary B.8.7, printed p. 683 / PDF p. 714, identifies
`T^0(O)` with the norm image `T(K)^0` using `S = R_{L/K}(T_L)`. The assembly
follows this route with the Library's actual relative identity component.
The registered corrections `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, amend Appendix B only in Section B.10; PDF pp. 24–25 leave
Proposition 2.5.8, Lemma 2.5.12 and Definition 2.5.13 unchanged, and the
corrections pass from Section 2.6 to Section 2.11, so Section 2.10 is
unchanged.

## Proof of the assembly

`unramifiedTorusIwahoriModelAssembly` proves the assembly statement. Fix the
target's data `F`, `T`, `L` and the splitting hypothesis `hL`.

1. `fixedFieldIntegers_strictHenselian F` packages the published facts that
   `O` is a discrete valuation ring (`fixedFieldIntegersIsDVR_of_valuesFromBase`
   with `fixedFieldValuesFromBase`), Henselian
   (`fixedFieldIntegersIsHenselian`), and has an algebraically closed, hence
   separably closed, residue field (`fixedFieldResidueIsAlgClosure`).
2. `geometricallyConnected_of_isSplitTorus_baseChanged` shows that
   `T.toGrp.X.hom` is geometrically connected. The split base change is
   reductive (`IsSplitTorus.isReductive`), hence geometrically connected
   (`IsReductive.geometricallyConnected`). Its structure morphism is the
   second projection of the pullback along `Spec L → Spec K`, which is
   surjective because `Spec K` has one point and `Spec L` is nonempty.
   The ported theorem `GeometricallyConnected.descendsAlong_surjective`
   descends the property through the flipped pullback square.
3. Input 2 gives a smooth `M` with `M.integralPoints = T(K)^1`; its torus
   hypothesis is witnessed by `L` and `hL`. The published
   `RelativeIdentityComponent.smoothExistence` gives a relative identity
   component `i : H ⟶ M.group` with `H` smooth and geometrically connected.
   Since `T` is geometrically connected, `M.neutralModel hM hi hH` is an
   actual `IntegralModel O K T.toGrp` with group `H` (module
   `Langlands.GroupScheme.IntegralModel.RelativeComponentConstruction`). It
   is the produced model: it is smooth by `hH` and has geometrically
   connected fibres by the geometric connectedness of `H.X.hom`.
4. Input 4 gives `S`, `W`, `n` with `W` smooth, geometrically connected, and
   `W.integralPoints.map (rationalPoints.map n) = T(K)^0`. The published
   `torusNormIwahori_le_characterValuationKernel`, with
   `intermediateValuation_conjugate`, gives `T(K)^0 ≤ T(K)^1 = M.integralPoints`.
5. `exists_hom_of_map_integralPoints_le` applies input 1 to `W`, `M` and `n`
   and returns `φ : W.Hom M n`.
6. `IsRelativeIdentityComponent.exists_hom_lift`, applied to `φ.hom` and the
   geometrically connected `W.group`, gives `y : W.group ⟶ H` with
   `y ≫ i = φ.hom`.
7. The inclusion `M⁰.integralPoints ≤ T(K)^0` is input 3 applied to the
   neutral model.
8. The reverse inclusion is `map_integralPoints_le_neutralModel`. For an
   integral section `w` of `W`, naturality of integral points for `φ`
   (`Hom.integralPointMap_naturality`) gives
   `M.integralPointMap (φ.hom ∘ w) = n (W.integralPointMap w)`. Naturality
   for the model homomorphism `neutralInclusion` over `𝟙 T`, whose
   underlying map is `i`, gives
   `M.integralPointMap (i ∘ (y ∘ w)) = M⁰.integralPointMap (y ∘ w)`. Since
   `i ∘ (y ∘ w) = φ.hom ∘ w`, the section `y ∘ w` of `H` maps to
   `n (W.integralPointMap w)`. Hence the image of `W.integralPoints` under
   `n`, which is `T(K)^0` by input 4, lies in `M⁰.integralPoints`.

`le_antisymm` combines steps 7 and 8 into the literal equality
`M⁰.integralPoints = torusNormIwahori K L (intermediateValuation F L) T`.

The module also proves `neutralModel_integralPoints_le`: the neutral model's
integral points lie in those of the full model, by `Hom.map_mem_integralPoints`
for `neutralInclusion`. The assembly does not use it.

## Technical note

The assembly theorem uses `set_option maxHeartbeats 1600000`. The four
statements are elaborated in different modules, and nested proof arguments
inside their instance terms are abstracted into different auxiliary
constants. Unifying the resulting terms is correct by proof irrelevance but
expensive, and the heartbeat count is cumulative over the declaration.

## Not asserted

The module asserts no Néron mapping property, uniqueness of models, or
independence from `L`. It constructs no Weil restriction model, no smooth
model of `T(K)^1` and no norm surjectivity. Those are the open inputs 2–4.
Input 1 is a published proposition with its own proof task.
