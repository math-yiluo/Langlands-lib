# Apartments of the restricted building are polysimplicial

For a supplied abstract Tits system `h : IsTitsSystem B N π S`, this module
works with the polysimplicial complex `h.restrictedComplex` of the component
buildings from `TitsRestrictedPolysimplicial`. It proves that the facets of
each restricted apartment form a polysimplicial complex in the sense of the
existing `AbstractBuilding.IsPolysimplicial` (KP Remark 1.5.4). This is the
polysimplicial part of KP Proposition 1.5.18(1),(3) for the apartments
`A' = B' ∩ A`. The apartments are the existing `restrictedApartment B π S a`:
the parabolic subgroups `(a n) G_X (a n)⁻¹` with `n ∈ N` and `X` admissible.
All results are internal deductions from the existing Tits-system API, the
frozen `TitsSystemExchange` and `TitsRestrictedPolysimplicial` candidates, and
the existing criterion `isPolysimplicial_of_coordinateMixingClosed` of
`PolysimplicialSubcomplex`.

## Weyl-group mixing

`exists_forall_inv_mul_mem_closure` is the Weyl-group counterpart of
`exists_forall_inv_mul_mem`. When `S` is finite, every family `w_c ∈ W`
indexed by the components has a common `v` with
`w_c⁻¹ v ∈ W_{S \ S_c}` for all `c`. The proof is induction over a finite set
`J` of components. With `T` the union of the components in `J`, the existing
decomposition `exists_mul_eq_of_commute` writes `v⁻¹ w_m = u t` with
`u ∈ W_{S \ T}` and `t ∈ W_T`. The new point is `v u`: for `c ∈ J` the factor
`u` lies in `W_{S \ T} ≤ W_{S \ S_c}`, and `w_m⁻¹ v u = t⁻¹ ∈ W_T ≤ W_{S \ S_m}`.

## Component faces

`componentFace_eq_of_inv_mul_mem` shows that the face of the component `c`
attached to `x G_X x⁻¹` equals the face attached to `y G_Y y⁻¹`, provided that
`x⁻¹ y ∈ G_{S \ S_c}` and `X`, `Y` contain the same elements of `S_c`. Both
faces are computed by `conjugate_le_iff_of_isComponentVertex`. For `s ∈ S_c`,
the element `x⁻¹ y` lies in `G_{S \ {s}}`, so `maximalParabolic_mul_of_mem`
identifies the two vertices `x G_{S \ {s}} x⁻¹` and `y G_{S \ {s}} y⁻¹`.

`eval_image_restrictedBox` states that for admissible `P` the projection of
`restrictedBox P` to the coordinate `c` is `componentFace c P`, because the
product is nonempty.

## Apartments

`restrictedApartmentBoxes a` is the set of products `restrictedBox P` for
`P ∈ restrictedApartment B π S a`.

`isSubcomplex_restrictedApartmentBoxes` proves that it is a subcomplex of
`restrictedComplex.facets` (KP Definition 1.5.1(7)). Every member is a facet
because apartment parabolic subgroups are admissible. If a facet `C` is
contained in `restrictedBox P` with `P` in the apartment, then `C` is
`restrictedBox P'` for an admissible `P'` with `P ≤ P'`. The existing lemma
`mem_restrictedApartment_of_le` puts `P'` in the same apartment.

`restrictedApartmentBoxes_nonempty` uses the Borel conjugate `a B a⁻¹`, of
the admissible empty type.

`isCoordinateMixingClosed_restrictedApartmentBoxes` proves the existing
coordinate-mixing condition. Given apartment parabolic subgroups
`P_c = (a n_c) G_{X_c} (a n_c)⁻¹`, one for each component, the Weyl-group
mixing gives `v` with `π(n_c)⁻¹ v ∈ W_{S \ S_c}`. Choose `m ∈ N` over `v`, and
let `Y` be the union of the sets `S_c ∩ X_c`. Then `Y` is admissible, and
`(a m) G_Y (a m)⁻¹` lies in the apartment. Its component faces are those of
the `P_c`: `(a n_c)⁻¹ (a m) = n_c⁻¹ m` is a normalizer element over
`W_{S \ S_c}`, hence lies in `G_{S \ S_c}`, and `Y` agrees with `X_c` on
`S_c`. So the product of the chosen component faces is a facet of the
apartment.

`isPolysimplicial_restrictedApartmentBoxes` combines these three facts with
`isPolysimplicial_of_coordinateMixingClosed`. Every restricted apartment is
therefore order isomorphic to the facets of a finite product of simplicial
complexes.

## Scope

These are statements about an arbitrary supplied Tits system with finite `S`.
They do not identify these apartments with apartments of a valuation
quotient or construct a realization. They prove no witness of
`RootValuationBuildingConstructionStatement`.
