# Points of separated finite type spaces with values in products of complete local rings

Author: Worker 105.

The general form of Conrad's Proposition 5.2 used in the proof of
`Langlands.Global.AdelicSpaceLevelPointsStatement`. Let `X` be a separated algebraic space of
finite type over `Spec C` and `O i` (`i : ι`) complete local `C`-algebras, for example fields
or complete discrete valuation rings. Then `X(∏ O i) → ∏ X(O i)` is bijective. This general
form is derived content: Conrad states the case of the adelic level ring (printed p.13).

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPoints`.

- `isSurjective_map`, `IsSurjective.comp`: maps of represented presheaves along surjective
  morphisms are surjective, and surjective maps compose (the relative-property framework, as
  for the Library's `isEtale_map` and `IsEtale.comp`).
- `isQuasiSeparated_of_isSeparated`: a separated space is quasi-separated (closed immersions
  are quasi-compact).
- `exists_affine_atlas`: a space of finite type over `Spec C` has an étale surjective chart from
  an affine scheme. Cover the quasi-compact atlas by finitely many affine opens and take their
  disjoint union (Mathlib: finite coproducts of affine schemes are affine; étaleness is local
  on the source).
- `exists_pi_point`: points of an affine scheme with values in `∏ B i` are families of points
  (`affineSchemePointEquiv`, `affineSchemePointEquiv_changeRing`).
- `separatedProductPoints_surjective`: surjectivity, following Conrad's proof on printed
  pp.13–14.
  1. Choose an affine étale surjective chart `U → X` (`exists_affine_atlas`).
  2. `ProductPointsLocalLift.exists_local_lift` gives a rank `d > 0` and, for each `i`, a finite
     free `O i`-algebra `B i` of rank `d` with a point of `U` over the image of `x i`.
  3. These assemble to a point of `U` with values in `∏ B i` (`exists_pi_point`). Its image
     `x'` in `X(∏ B i)` restricts on each factor to the image of `x i`.
  4. For each `i`, the two images of `x'` in `X(B i ⊗ B i)` are the two images of `x i`. These
     agree because `O i → B i ⊗ B i` is the same through either factor. So
     `ProductPointsDescent.exists_changeRing_eq` descends `x'` to some `x ∈ X(∏ O i)`.
  5. The factor of `x` at `i` and `x i` have the same image in `X(B i)`. Pullback along the
     fppf cover `Spec B i → Spec O i` is injective (`ProductPointsDescent.pullback_injective`),
     so they are equal.
- `separatedProductPoints_bijective`: with the Library's `separatedProductPoints_injective`.
