# The big cell over a ring, from its residue-field fibres

This module proves `Langlands.GroupScheme.localSplitBigCell`, which is the
Library proposition `LocalSplitBigCellStatement` of
`Langlands.GroupScheme.Reductive.LocalSplitCell`, unchanged.

Let R be a commutative ring and G a reductive group over Spec R with
`IsAffineHom G.X.hom`. Let `i` be a closed coordinate split torus that is a
maximal torus on every residue-field fibre, and let P be a fibrewise root
datum for `i`. Fix a base `bs` of P, root parametrizations `u α` for all roots,
and enumerations `neg` of the roots that are not positive and `pos` of the
positive roots. Then the big-cell map

  `cellMap i u neg pos : 𝔾ₐᵐ × T × 𝔾ₐⁿ ⟶ G`,
  (v, t, w) ↦ (∏_r u_{neg r}(v_r)) · i(t) · (∏_r u_{pos r}(w_r)),

is an open immersion. The statement assumes that R is local and reduced. The
proof uses neither assumption.

The module also provides the base change of root parametrizations to a field,
for use elsewhere in the same task.

## Provenance

This is an internal proof, written for the local-ring Isomorphism Theorem task
(ab10ec3c). The result is the open-cell part of Conrad, *Reductive group
schemes* (2014), Theorem 5.1.13 (p.143), in the split setting of the Library's
`LocalSplitCell`. Conrad builds the open cell over an arbitrary base by the
dynamic method. The Lean proof instead reduces to fields. It applies the
fibrewise criterion `Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise`
to the big-cell map, and on each residue-field fibre it uses the field big cell
`Langlands.GroupScheme.SplitBigCell.isOpenImmersion_of_points`. Both results
are in the Library, the latter based on Milne, *Algebraic Groups* (2017),
Theorem 21.84. The work in this module is to identify the fibre of the
big-cell map with the field big cell.

Throughout, k is a field with an R-algebra structure, b is
`algebraBaseMap R k : Spec k ⟶ Spec R`, and G_k is
`(GroupScheme.baseChange b).obj G`. Points of a base change are compared with
points of the original object through `GroupScheme.baseChangePointsEquiv`,
written bcPE below. For an object Z over Spec k, `(Over.map b).obj Z` has the
same underlying scheme as Z, so global functions on both are the same ring.

## Base change of root parametrizations

Section `RootBaseChange`:

- `gaCoordinates k Z`: a point of the base change of 𝔾ₐ over Z gives, through
  bcPE, a point of 𝔾ₐ over `(Over.map b).obj Z`. Its coordinate is a global
  function on Z. `isNaturalVectorCoordinates_gaCoordinates` says these
  coordinates are natural in Z (`baseChangePointsEquiv_naturality`).
- `gaIso k : (GroupScheme.baseChange b).obj (Ga R) ≅ Ga k` is the
  isomorphism defined by these coordinates (`RelativeRoot.vectorGroupIso`).
  `baseChangePointsEquiv_scalarPoint` says it sends the scalar point c over k
  to the scalar point c over R.
- `baseChangeRoot k u := (gaIso k).inv ≫ (GroupScheme.baseChange b).map u` is
  the base change of a map `u : 𝔾ₐ ⟶ G`.
  `baseChangePointsEquiv_rootPoint` identifies bcPE of
  `rootPoint (baseChangeRoot k u) Z c` with `rootPoint u ((Over.map b).obj Z) c`.
  The proof uses `baseChangePointsEquiv_comp`. `baseChangePointsEquiv_orderedProduct`
  is the same statement for ordered products, since bcPE is multiplicative.
- `isRepresentedBy_baseChangeRoot`: if u represents the root subgroup of `i`
  for the exponent character m, then `baseChangeRoot k u` represents the root
  subgroup of `splitTorus.baseChangeHom (K := k) G I i` for the same exponent
  character. The proof base-changes the representation
  (`IsRepresentedBy.baseChange`) and uses `RelativeRoot.subgroup_baseChange`.
  It transports along the canonical torus comparison
  `splitTorus.commBaseChangeIso` with `subgroup_comap_of_transport` and
  `splitTorus.exponentCharacter_baseChange`. Finally it precomposes with
  `gaIso` (`SubgroupFunctor.range_iso_comp`).
- `baseChangePointsEquiv_torus`: bcPE of `t ≫ i_k`, for
  `i_k = splitTorus.baseChangeHom (K := k) G I i`, is bcPE of
  `t ≫ (splitTorus.baseChangeIso b I).inv` followed by i.
  `charValue_exponentCharacter_baseChange` says exponent characters take the
  same values on these two torus points. It is proved with
  `splitTorus.pointsEquiv_exponentCharacter` and
  `splitTorus.pointsEquiv_baseChangeIso_hom`.
- `isRootParametrization_baseChangeRoot`: `IsRootParametrization i m u`
  implies `IsRootParametrization i_k m (baseChangeRoot k u)`. Representation
  is the result above. Closedness follows from `IsClosedSubgroup.baseChange`
  and the isomorphism `gaIso`. Equivariance is checked after applying bcPE,
  using the three point identities above and the equivariance of u.

## The cell source and its base change

Section `Cell`:

- `coordTriple x = (negCoord x, torusCoord x, posCoord x)` for a point x of
  `cellObj R I m n`. `coordTriple_bijective` says this is a bijection on the
  points of every test object, since the cell source is a product of vector
  groups and a split torus.
- `fibreObj R I m n k` is the base change of the cell source to k.
  `fibreCounit` is the universal point, the adjunction transpose of the
  identity under `Over.mapPullbackAdj b`. Its coordinates are `fibreNeg`,
  `fibrePos` and, through bcPE and `splitTorus.baseChangeIso`, `fibreTorus`.
- `fibreCoords_bijective`: for every test object Z over Spec k, the map
  z ↦ (z^* fibreNeg, z ≫ fibreTorus, z^* fibrePos) is bijective. It is the
  composite of the adjunction bijection (`homEquiv_symm_eq` rewrites it as
  composition with `fibreCounit`), `coordTriple_bijective` over
  `(Over.map b).obj Z`, and bijections on the torus factor.

## The fibre of the big-cell map

`pullback_map_cellMap`: the base change of `cellMap i u neg pos` to k is

  `orderedProduct (baseChangeRoot k ∘ u) neg _ fibreNeg *
     (fibreTorus ≫ i_k) * orderedProduct (baseChangeRoot k ∘ u) pos _ fibrePos`.

Both sides are checked after applying the injective map bcPE. The left side
becomes `fibreCounit ≫ cellMap` (`Adjunction.homEquiv_naturality_right_symm`),
which `comp_cellMap` evaluates. The right side is evaluated factor by factor
by the identities of the previous sections.

## The root datum on a field fibre

Section `RootDatum` uses `IsFibrewiseRootDatumOf.field`:

- `relativeRoots_baseChangeHom`: the relative roots of i_k are the exponent
  characters of the roots of P. `exponentCharacter_injective` says distinct
  exponents give distinct characters.
- `reducedRays`: the roots of i_k satisfy `SplitBigCell.ReducedRays`. If
  p • a = q • b for roots a, b and positive integers p, q, then a and b are
  linearly dependent. Since P is reduced, b = a or b = −a. The second case
  gives (p + q) a = 0, which is impossible for a nonzero root of ℤ^I. In the
  first case p = q.
- `cellCocharacter k bs` is the exponent cocharacter of
  `IntegralWeylVector.positiveRootSum P.flip bs.flip`, the sum of the positive
  coroots. By `pairing_cellCocharacter`, its pairing with the root α is
  `2 * bs.height α`. The proof writes α as an integral combination of simple
  roots (`exists_root_eq_sum_int`, `height_eq_sum`). It then uses that each
  simple root pairs to 2 with the sum of the positive coroots
  (`pairing_positiveRootSum_simple` for the reduced datum P.flip).
- Heights of roots are nonzero, and positive exactly on positive roots. So
  this cocharacter is generic (`isGenericCocharacter_cellCocharacter`). The
  non-positive roots are exactly the roots with negative pairing (`range_neg`),
  and the positive roots are those with positive pairing (`range_pos`).

## The big cell

- `isOpenImmersion_fibre`: for every field k with an R-algebra structure, the
  base change of the big-cell map to k is an open immersion. After
  `pullback_map_cellMap`, this is `SplitBigCell.isOpenImmersion_of_points`
  applied to:
  - G_k, which is connected reductive by `IsReductive.isConnectedReductive_baseChange`;
  - the split torus i_k, which is maximal by
    `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`;
  - the cocharacter `cellCocharacter k bs` and the base-changed root maps,
    which represent the root subgroups by `isRepresentedBy_baseChangeRoot`;
  - the source `fibreObj` with the coordinates of `fibreCoords_bijective`.
- `localSplitBigCell`: the cell source is smooth over Spec R, as a product of
  vector groups (`Corepresented.smooth_groupScheme_iff`) and a split torus
  (`smooth_tensor`, `smooth_splitTorus`), so it is flat and locally of finite
  presentation. G is smooth, hence locally of finite type. By
  `isOpenImmersion_of_fiberwise`, it suffices that every residue-field fibre is
  an open immersion. For a point s, the residue field κ(s) becomes an
  R-algebra through `Spec.preimage` of `fromSpecResidueField s`, and then
  `algebraBaseMap R κ(s) = fromSpecResidueField s` by `Spec.map_preimage`. So
  `isOpenImmersion_fibre` with k = κ(s) gives the fibre.

`localSplitBigCell` uses only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
