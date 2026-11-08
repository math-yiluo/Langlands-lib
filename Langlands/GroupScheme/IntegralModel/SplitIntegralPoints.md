# Integral points on closed root groups and closed split tori of an integral model

Let `R` be a domain, `K` its specified fraction field, and
`M : IntegralModel R K G` a supplied model of the group scheme `G` over
`Spec K`. All rings and schemes use one arbitrary universe `u`. This module
computes which generic points of a closed root group `𝔾ₐ ⟶ M.group` and of a
closed split torus `splitTorus (Spec R) I ⟶ M.group` are integral points of the
model. It applies the closed-subgroup integrality of
`Langlands.GroupScheme.IntegralModel.ClosedSubgroupIntegralPoints` to these two
subgroups and reads the result in coordinates.

## Base change of sections

`GroupScheme.baseChangePointsEquiv_baseChangeSectionHom` holds for any
morphism of schemes `b : T ⟶ S` and group scheme `G` over `S`. It states that
the base change `baseChangeSectionHom b G x` of a section `x` of `G`, read back
as a point of `G` through the pullback point correspondence
`baseChangePointsEquiv b G (Over.mk (𝟙 T))`, is the composite of `x` with the
structure map `b`, viewed as a morphism over `S`. It is the Library equation
`baseChangeSectionHom_fst`, restated on points.

## Closed root groups

Let `u : Ga R ⟶ M.group` be a homomorphism from the additive group `𝔾ₐ` over
`Spec R`. Here `rootPoint u Z c` is the Library value `u(c)` of `u` at a global
function `c` of a test scheme `Z`, and `gaIso K` is the Library identification
of the base change of `𝔾ₐ` along `Spec K ⟶ Spec R` with `𝔾ₐ` over `Spec K`.

- `genericRootHom u : Ga K ⟶ G` is the generic fibre of `u`: the inverse of
  `gaIso K` followed by `genericHom u`, which is the base change of `u` followed
  by the generic identification `M.genericIso.hom`.
- `baseChangeSectionHom_scalarPoint` states that the base change of the
  `𝔾ₐ`-section with coordinate `r` on `Spec R` is the `𝔾ₐ`-section over `Spec K`
  whose coordinate is the restriction of `r` along `Spec K ⟶ Spec R`, carried
  through the inverse of `gaIso K`.
- `integralPointMap_rootPoint` states that `M.integralPointMap` sends the
  integral section `u(r)` to the generic value `(genericRootHom u)(r|K)` at the
  restricted coordinate.
- `rootPoint_genericRootHom_mem_integralPoints_iff` assumes that `u` is a
  closed subgroup (`IsClosedSubgroup u`). For a global function `c` on
  `Spec K`, the generic value `(genericRootHom u)(c)` lies in `M.integralPoints`
  if and only if `c` is the restriction of a global function on `Spec R`.
- `genericRootValue u c` is the generic value `(genericRootHom u)(c)` at an
  element `c : K`, transported to global functions by `Scheme.ΓSpecIso`.
- `genericRootValue_mem_integralPoints_iff` is the field form: for a closed
  subgroup `u` and `c : K`, the point `genericRootValue u c` lies in
  `M.integralPoints` if and only if `c` lies in the image `(algebraMap R K).range`
  of `R`.

The forward implication of the closed-subgroup statement uses
`exists_eq_of_integralPointMap_eq`. It produces an integral section of `𝔾ₐ`
whose base change is the given generic `𝔾ₐ`-point. Every section of `𝔾ₐ` is
`scalarPoint` of a unique coordinate (`LocalRootGroup.scalarPoint_bijective`),
so comparing coordinates after cancelling `gaIso K` gives the function on
`Spec R`. The reverse implication is `integralPointMap_rootPoint`. The field form
translates between global functions and ring elements with the naturality of
`Scheme.ΓSpecIso`.

## Closed split tori

Let `I` be a finite type and `i : splitTorus (Spec R) I ⟶ M.group` a
homomorphism. Points of a split torus are read through the Library coordinate
equivalence `splitTorus.pointsEquiv`, which sends a point to its family of unit
coordinates.

- `genericSplitTorusHom i : splitTorus (Spec K) I ⟶ G` is the generic fibre of
  `i`: the inverse of the Library base-change isomorphism
  `splitTorus.baseChangeIso (Spec.algebraMap R K) I` followed by `genericHom i`.
- `pointsEquiv_baseChangeSectionHom` states that the base change of an integral
  point `h` of the split torus, carried to `splitTorus (Spec K) I` by that
  isomorphism, has as coordinates the restrictions along `Spec K ⟶ Spec R` of
  the unit coordinates of `h` in `Γ(Spec R, ⊤)`. Its proof combines
  `splitTorus.pointsEquiv_baseChangeIso_hom`, the definition of the base-change
  point model and `splitTorus.pointsEquiv_naturality` with the base-change
  statement of the first section.
- `splitTorusPoint_mem_integralPoints_iff` assumes that `i` is a closed
  subgroup. For a family `t` of units of `Γ(Spec K, ⊤)`, the image under
  `genericSplitTorusHom i` of the `K`-point with coordinates `t` lies in
  `M.integralPoints` if and only if every coordinate `t j` is the restriction of
  a unit of `Γ(Spec R, ⊤)`.
- `genericSplitTorusValue i t` is that generic image for a family
  `t : I → Kˣ` of field units, transported to global functions by
  `Scheme.ΓSpecIso`.
- `genericSplitTorusValue_mem_integralPoints_iff` is the field form: for a
  closed subgroup `i` and `t : I → Kˣ`, the point `genericSplitTorusValue i t`
  lies in `M.integralPoints` if and only if for every `j` there is a unit
  `s : Rˣ` with `algebraMap R K s = t j`.

The forward implication again uses `exists_eq_of_integralPointMap_eq` and
reads the coordinates of the integral torus section it supplies through
`pointsEquiv_baseChangeSectionHom`. For the reverse implication the integral
torus section with the given unit coordinates is built with the inverse of
`splitTorus.pointsEquiv`. Its base change equals the given generic point
because the two have the same coordinates. Its image is integral by
`subgroupPointMap_apply`.

## Provenance

These are the standard facts that the integral points of the additive group
and of a split torus over a domain `R` are `R` and `(Rˣ)^I`, and that, through a
closed embedding into the model, the integral points of the model on such a
subgroup are exactly the integral points of the subgroup. They are internal.
The proofs use only the Library `IntegralModel` interfaces, the closed-subgroup
integrality of `ClosedSubgroupIntegralPoints`, the `𝔾ₐ` point and base-change
interfaces of `LocalSplitCell`, `LocalSplitBigCellProof` and
`LocalRootGroupParam`, and the split-torus point model and base change of
`Torus.Split` and `Torus.SplitLatticeBaseChange`. They are inputs for comparing
the integral points of a hyperspecial model with stabilizers in the building
(root groups `u_a(R)` and the torus `T(R)`). The module proves no statement about
buildings, stabilizers, valuations or the existence of closed root groups or
closed split tori in a given model.
