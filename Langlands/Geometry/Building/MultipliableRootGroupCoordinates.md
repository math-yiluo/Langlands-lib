# Valued scheme-level unitary coordinates of multipliable root groups

Lean module: `Langlands.Geometry.Building.MultipliableRootGroupCoordinates`.

This module states the scheme-level coordinate description of a *multipliable*
relative root group, that is, a root `b` whose double `2 • b` is also a relative
root, over the maximal unramified field. It is the scheme-level form of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023):

- Construction 2.9.16, display (2.9.3) (printed page 117): for a relative root
  `a` of type R2 with lifts `ã, ã'` and `b̃ = ã + ã'`, a Chevalley–Steinberg system
  gives an isomorphism of `k`-groups `R_{k_b̃/k} U_{k_ã/k_b̃} → U_a`;
- Construction 6.1.17 (printed pages 205–206): through this isomorphism the
  unshifted Chevalley valuation is `φ_a((u, v)) = ω(v) / 2`, where `ω` is the
  fixed valuation on `k_ã` extending that of `k`;
- Proposition 6.1.19 (printed page 206): the Chevalley valuation is a valuation of
  the root datum, so it is a point of the apartment.

The module only defines a record and an existence proposition. It proves neither
existence nor anything about integral models. Whether the existence proposition
holds is left open. Packaging the KP data as a record over the Library's actual
building data `MaximalUnramified.BuildingData` is internal to this project.

## Instances on the unitary parameter group

`SU3Root.unitaryParameterGroup_isAffine` and
`SU3Root.unitaryParameterGroup_locallyOfFiniteType`. For a separable quadratic
extension `L / k`, the Library's unitary parameter group
`SU3Root.unitaryParameterGroup k L`, i.e. `U_{L/k}`, is affine and locally of
finite type over `k`. By definition it is the bilinear coordinate group scheme of
the canonical coordinate data `SU3Root.canonicalCoordinateData k L`. The proofs
unfold this definition and apply the Library facts `BilinearCoordinate.isAffineHom`
(the structure morphism is affine, so the total space is affine over the affine
base) and `BilinearCoordinate.locallyOfFiniteType`. These instances are needed to
form the Weil restriction `AffineWeil.groupScheme K E (unitaryParameterGroup E L)`.

## The record

`ValuedUnitaryRootGroupCoordinates B b`. Fix:

- a nonarchimedean local field `F` with maximal unramified field
  `K = inertiaFixedField F`;
- an affine group scheme `G` over `Spec K`;
- building data `B : MaximalUnramified.BuildingData F G`, with maximal split torus
  `B.i : B.S ⟶ G` and apartment `B.Apartment`;
- a character `b` of `B.S`.

A term of the record consists of:

- fields `base` (written `E`) and `extension` (written `L`) in universe `u`, with
  algebra structures `K → E`, `E → L`, `K → L` forming a scalar tower;
- the conditions that `E / K` is finite and separable, `L / E` is quadratic and
  separable, and `L / K` is separable;
- `inclusion`, a homomorphism of `K`-group schemes from the Weil restriction
  `R_{E/K} U_{L/E}` (`AffineWeil.groupScheme K E (SU3Root.unitaryParameterGroup E L)`)
  to `G`;
- `isRootSubgroup`: `inclusion` represents the relative root subgroup
  `RelativeRoot.subgroup B.i b`, i.e. the root group `U_b` (in the sense of the
  Library predicate `IsRepresentedBy`);
- `origin`, a point of the apartment `B.Apartment`;
- `depth`: for every rational unitary parameter `p = (u, v)` in
  `SU3Root.rationalParameters E L` (the pairs in `L²` with `v + σ(v) = u σ(u)`,
  `σ` the nontrivial automorphism of `L / E`), the value at `origin` of `b` on the
  image under `inclusion` of the `K`-point corresponding to `p` equals
  `SU3Root.towerDepth K E L v hH p`. The `K`-point is obtained from `p` by the
  Library equivalences `SU3Root.unitaryRationalPointsEquiv E L` (rational
  parameters as `E`-points of `U_{L/E}`) and `AffineWeil.sectionsEquiv K E _`
  (`E`-points of `U_{L/E}` as `K`-points of its Weil restriction). Here `v` is
  `MaximalUnramified.valuation F` and `hH` is the henselian property of its
  valuation ring. By definition, `towerDepth K E L v hH (u, v') = ω(v') / 2`, where
  `ω = FieldTheory.henselianSeparableAddValuation v hH L` is the unique extension
  to `L` of the valuation of `K` normalized by `ω(K^×) = ℤ`. Halving uses the
  convention `⊤ / 2 = ⊤`.

This matches KP Construction 6.1.17 with `k = K`, `k_b̃ = E` and `k_ã = L`. The KP
valuation `ω` on `k_ã` is the extension of the valuation on `k`. Here we use the
normalization `ω(K^×) = ℤ` of the Library's integer valuation on `K`. This is the
normalization `IntegerValuation.order (MaximalUnramified.valuation F)` with which the
supplied apartment `B.apartment` is formed. The record keeps only the
properties used downstream:

- KP's isomorphism (2.9.3) is replaced by a homomorphism representing the root
  subgroup;
- the Chevalley valuation is recorded only through its value on the coordinate
  points at one apartment point.

The double root `2 b` and its subgroup `U^0_{L/E}` are not recorded.

## The existence proposition

`MultipliableRootGroupCoordinatesExistenceStatement`, at universe `u`. For every
nonarchimedean local field `F`, every affine group scheme `G` over
`Spec (inertiaFixedField F)` with building data `B : MaximalUnramified.BuildingData
F G`, and every relative root `b ∈ relativeRoots B.i` with `2 • b ∈ relativeRoots
B.i`, the type `ValuedUnitaryRootGroupCoordinates B b` is nonempty.

In KP this is the combination of Construction 2.9.16 and Construction 6.1.17 /
Proposition 6.1.19 for the quasi-split group `G` over `K` (the group is
quasi-split because `K` is maximal unramified), together with the identification
of the Chevalley valuation as a point of the supplied apartment. The proposition
is stated here so that the multipliable case of KP Lemma C.5.3 can be reduced to
it separately; this module does not prove it.
