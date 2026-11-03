# Limits of multiplicative-group orbits in a scheme with an action

This internal module adapts two published conjugation-orbit arguments to an
arbitrary multiplicative-group action on a scheme. The conjugation versions are
`Dynamic.HasLimit.mem_centralizer` (in `Dynamic/Uniqueness.lean`) and
`Dynamic.orbitOpenLift` (in `Dynamic/OrbitOpenLift.lean`). Here the group scheme
is replaced by any `X : Over S` with an action
`b : SchemeAction (Gm S).toGrp X`. A cocharacter `λ` of a group scheme `G`
acting on `X` by `a` enters through the restricted action `a.restrict λ`.

## Orbits and their extensions

For a point `x : T ⟶ X` over `S`, `gmOrbit b x : T ⊗ (Gm S).X ⟶ X` is the
orbit map `(t, s) ↦ s • x(t)`. `whiskerRight_gmOrbit` proves that orbit maps
are natural in the test scheme `T`.

`IsGmOrbitExtension b x e` states that `e : T ⊗ AffineLine.scheme S ⟶ X`
restricts to the orbit map along the inclusion of the multiplicative group in
the affine line, `T ◁ AffineLine.unitInclusion S`. Two facts hold for every
base: `IsGmOrbitExtension.whiskerRight` restricts an extension along a
morphism of test schemes, and `IsGmOrbitExtension.eval_one` shows that the
extension takes the value `x` at the unit section.

## Separated targets: uniqueness, equivariance and the fixed limit (L1)

From here on `X` is separated over `S`. Then:

- `IsGmOrbitExtension.unique`: an orbit map has at most one extension. This is
  the published `AffineLine.hom_ext_of_unitInclusion`.
- `IsGmOrbitExtension.scale`: the extension is equivariant. On
  `(T ⊗ Gm) ⊗ 𝔸¹` the morphisms `(t, s, v) ↦ s • e(t, v)` and
  `(t, s, v) ↦ e(t, s v)` agree after restriction to `(T ⊗ Gm) ⊗ Gm`, by the
  action law `act_mul` and naturality. Uniqueness of extensions then makes them
  equal.
- `IsGmOrbitExtension.isFixed_evalZero`: the zero value `Dynamic.evalZero e`
  is fixed in the all-test sense `SchemeAction.IsFixed`. The proof evaluates the
  scaling identity at the zero section, using
  `AffineLine.lift_zeroSection_scale`, and applies
  `SchemeAction.isFixed_iff_universal`.
- `IsGmOrbitExtension.eval_scale` evaluates the scaling identity on arbitrary
  test points `c : Q ⟶ T`, `a : Q ⟶ Gm` and a global section `v`.

## Stable opens: lifting the extension (L2)

`IsGmStable b j` says that a subscheme `j : U ⟶ X` is stable under the action
on every test scheme: for each `Q`, each `a : Q ⟶ Gm` and each `z : Q ⟶ U`,
the point `a • (z ≫ j)` factors through `j`. `IsGmStable.factors_iff` uses
`a` and `a⁻¹` to show that `y` factors through `j` exactly when `a • y` does.
This part needs neither separatedness nor a field base.

Over a field `k`, with `T = Spec k` as the identity object over `Spec k`:

- `IsGmOrbitExtension.fieldEvaluation_scale` evaluates the scaling identity at
  field-valued points: evaluating at `a v` equals acting by the unit `a` on
  evaluation at `v`.
- `IsGmOrbitExtension.isScalarInvariantOpen` proves that, for a stable open
  immersion `j`, the pullback of `j.left.opensRange` along the polynomial
  presentation of `e` is a scalar-invariant open of the affine line, in the
  all-field sense `AffineLine.IsScalarInvariantOpen`. It uses
  `AffineLine.fieldTest_mem_opensRange_iff` and `IsGmStable.factors_iff`.
- `polynomialGmOrbitOpenLift` applies the published saturation lift
  `AffineLine.invariantOpenLift`. Its extra input is that the underlying point
  of `Dynamic.evalZero e` lies in `j.left.opensRange`; the result is packaged as
  a morphism over the base. `polynomialGmOrbitOpenLift_fac` is its
  factorization.
- `gmOrbitOpenLift` composes with `AffineLine.polynomialPointInv` to obtain a
  morphism `T ⊗ AffineLine.scheme (Spec k) ⟶ U` over the base, and
  `gmOrbitOpenLift_fac` proves `gmOrbitOpenLift … ≫ j = e`.

## Provenance and scope

The module is an internal deduction from the published orbit-uniqueness,
affine-line scaling and saturation constructions and the categorical action
laws of `SchemeAction`. Each proof follows the corresponding conjugation proof
in `Dynamic/Uniqueness.lean` or `Dynamic/OrbitOpenLift.lean`, with
conjugation replaced by the action. It adds no splitness, perfectness,
characteristic or cardinality premise. The module does not prove that an orbit
extension exists (that needs a properness input), and it does not construct
any stable open.
