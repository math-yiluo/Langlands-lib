# Statement: torsors spread out over rings of `S`-integers

`Langlands.GroupScheme.ArithmeticTorsorSpreadingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It uses:

- `FinitePlace F` from [`Global.Adelic`](../../Global/Adelic.md): Mathlib's
  `IsDedekindDomain.HeightOneSpectrum (𝓞 F)`, the finite places of the number field `F`.
- `(S : Set (FinitePlace F)).integer F`: Mathlib's ring of `S`-integers of `F`, the
  elements of `F` that are integral at every finite place outside `S`. For a finite set
  `S` this is the ring of `S`-integers `𝓞_{F,S}`.
- `IntegralModel R F G` from [`GroupScheme.IntegralModel`](../IntegralModel.md): a group
  scheme `M.group` over `Spec R` whose structure map is affine, flat and locally of finite
  type, together with an isomorphism `M.genericIso` from its base change along
  `Spec F ⟶ Spec R` to `G`.
- `enlargeModel F M hST` from
  [`IntegralModel.ArithmeticHomSpreading`](ArithmeticHomSpreading.md): for `S ⊆ T`, the
  base change of the model `M` along the inclusion `𝓞_{F,S} ⊆ 𝓞_{F,T}`, regarded as an
  integral model of `G` over `𝓞_{F,T}`.
- `ringBaseChange C D Y` from
  [`PointTopology.RingPointBaseChange`](../../AlgebraicGeometry/PointTopology/RingPointBaseChange.md):
  the pullback of a scheme `Y` over `Spec C` along `Spec D ⟶ Spec C` for a `C`-algebra
  `D`.
- Mathlib's `ModObj H.X Y` (a left action of the group object `H.X` on `Y` in the
  cartesian monoidal category of schemes over the base) and its shear morphism
  `ModObj.leftSMul H.X Y : H.X ⊗ Y ⟶ Y ⊗ Y`, `(g, y) ↦ (g • y, y)`.

As in the published
[`AlmostAllPlacesQuasiSplitStatement`](../Reductive/AlmostAllPlacesQuasiSplitStatement.md),
an fpqc torsor under a group scheme `H` over a base `B` is encoded as a scheme `Y` over `B`
with an action `ModObj H.X Y` whose structure map `Y.hom` is flat, surjective and
quasi-compact and whose shear is an isomorphism.

## Statement

Let `F : Type u` be a number field, `S` a finite set of finite places of `F`, `G` a group
scheme over `Spec F`, and `M` an integral model of `G` over the ring of `S`-integers
`𝓞_{F,S}`. Let `X` be a scheme over `Spec F` with an action `ModObj G.X X` such that
`X.hom` is flat, surjective and quasi-compact and `ModObj.leftSMul G.X X` is an
isomorphism. Then there are

- a finite set `T` of finite places with `S ⊆ T`,
- a scheme `Y` over `Spec 𝓞_{F,T}` and an action `ModObj (enlargeModel F M hST).group.X Y`
  of the enlarged model on `Y`,

such that `Y.hom` is flat, surjective and quasi-compact, the shear
`ModObj.leftSMul (enlargeModel F M hST).group.X Y` is an isomorphism, and there is an
isomorphism `ringBaseChange 𝓞_{F,T} F Y ≅ X` of schemes over `Spec F`.

The isomorphism of generic fibres is not required to respect the actions. No smoothness,
connectedness or reductivity of `G` or `M` is assumed.

## Provenance

This is a derived statement, a focused prerequisite for the torsor clause of
`AlmostAllPlacesQuasiSplitStatement`. It is the step "spread the torsor out to a torsor
over a ring of `S`-integers" in the route suggested for Brian Conrad, *Reductive group
schemes* (2014), Exercise 5.5.3(iii), pp.182–183 (registered as
`conrad-2014-reductive-group-schemes`), where it is stated that "any G-torsor over F admits
an F_v-point for all but finitely many v". Conrad gives no proof of the exercise.

The mathematics is the standard spreading out of objects of finite presentation over a
filtered limit of rings, from A. Grothendieck and J. Dieudonné, *Éléments de géométrie
algébrique IV, Troisième partie*, Publ. Math. IHÉS 28 (1966), registered as
`ega-iv3-grothendieck-dieudonne-1966` (printed page numbers; the PDF page is one less):

- Théorème 8.8.2, pp.28–29: schemes of finite presentation and morphisms between them
  descend to a stage of the limit, and two morphisms that agree in the limit agree at
  some stage.
- Théorème 8.10.5, pp.37–38: properties of a morphism of finite presentation, including
  being an isomorphism (i) and being surjective (vi), hold at some stage when they hold
  in the limit.
- Théorème 11.2.6, pp.123–124: flatness of a morphism of finite presentation holds at some
  stage when it holds in the limit.

Here the limit is `F = colim_T 𝓞_{F,T}` over finite sets `T ⊇ S` of finite places. A proof
along these lines: `G` is affine of finite type over `F`, so by fpqc descent along
`X ⟶ Spec F` (using `X ×_F X ≅ G ×_F X`) the scheme `X` is affine of finite presentation
over `F`. Spread `X`, the action morphism `G ×_F X ⟶ X` and the inverse of the shear to a
stage `𝓞_{F,T}`, enlarge `T` until the action axioms and the two inverse identities hold
(8.8.2), and until the spread-out structure map is flat (11.2.6). Its image is then open
and contains the generic point, so it contains a nonempty basic open set `D(r)` of
`Spec 𝓞_{F,T}`; enlarging `T` so that `r` becomes a unit makes the structure map
surjective. Quasi-compactness holds because the spread-out scheme is affine.
