# Reducing KP 8.4.15 to apartment subsets and compatible zero data

Module `Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction`.

## Purpose and provenance

The published host statement
`Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement.{u}` is the
statement of Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Proposition 8.4.15. Its subsets of the building are translates
`g · Ωa ⊆ g · closure Ωa'` of apartment subsets by a point
`g ∈ G(K)`, where `K` is the maximal unramified extension. Its group `G(K)^0`
is defined by an arbitrary zero datum `E : UnramifiedZeroDatum`.

This module reduces the host statement to a special case. In the special case
there is no translation (`g = 1`), and the torus of the zero datum represents
the centralizer of the maximal split torus of the building data. The reduction
uses two published statements that have no proof in the Library. They are
explicit hypotheses of the main theorem:

* `Langlands.Geometry.Building.UnramifiedQuasiSplitStatement.{u}`: every
  connected reductive group over `K = UnramifiedClosure F` is quasi-split;
* `Langlands.Geometry.Building.UnramifiedZeroPointsIndependenceStatement.{u}`:
  the subgroup `E.zeroPoints = H(K)^0` does not depend on the zero datum `E`
  (KP Lemma 2.6.24).

**This module does not prove the host statement.** It also does not prove the
special case `UnramifiedCompatibleModelKernelStatement` or either hypothesis.
The special case and the arrangement of this reduction are internal design by
Worker 4783 for Task 6203, which Worker 282 and Worker 4783 share. They are not
statements from the literature.

Notation: `K = inertiaFixedField F`, and `G_K = baseChanged F K G` is the base
change of the `F`-group `G` to `K`. `C` is building data for `G_K`
(`MaximalUnramified.BuildingData`), with apartment `C.Apartment`, map
`C.apartmentMap` into the reduced building, maximal split torus `C.i`, and
pointwise fixers `C.pointwiseFixer Y ≤ G_K(K)`.

## Replacing the torus of a zero datum

Namespace `Langlands.Geometry.Building.UnramifiedZeroDatum`. Here `H` is a group
scheme over `Spec K`.

* `withTorus E j hj`: for a zero datum `E` of `H` and a maximally split maximal
  torus `j : M → H` (`hj : IsMaximallySplitMaximalTorus j`, with `M` a
  commutative group scheme), this is the zero datum with torus `M` and embedding
  `j`. Its finite Galois splitting field `L ⊆ F^sep` of `M` is a choice from the
  published `exists_finiteGaloisSplittingField_inside`. The derived subgroup
  `E.d : E.D → H`, the simply connected cover `E.π : E.C → E.D` and its
  certificate are those of `E`. Affineness of `M` comes from `j` being a closed
  immersion into the affine group `H`.
* `withTorus_i` (simp, `rfl`): `(E.withTorus j hj).i = j`.
* `exists_isRepresentedBy_torusCentralizer E hquasi ha`: if `H` is quasi-split
  (`hquasi : IsQuasiSplit H`) and `a : A → H` is a maximal split torus
  (`ha : IsMaximalSplitTorus a`), then some zero datum `E'` of `H` satisfies
  `(torusCentralizer a).IsRepresentedBy E'.i`.

  *Proof.* The published `exists_maximalTorus_extension_of_finiteType` gives a
  maximal torus `j : M → H` and `f` with `f ≫ j = a`. Then `j` is maximally split
  by definition. The published, proved
  `Langlands.GroupScheme.quasiSplitMaximalTorusCentralizer` says that `j`
  represents the centralizer of `a`. Take `E' = E.withTorus j _`.

## Translation by `g`

Namespace `Langlands.BruhatTits.IntegralModels`, for an `F`-group `G` whose
structure morphism is affine. A private instance records that the base-changed
structure morphism of `G_K` is affine.

* `pointwiseFixer_smul_image_map_conj C g Y`: for `g ∈ G_K(K)` and a set `Y` of
  the reduced building, the image of `C.pointwiseFixer (g · Y)` under
  conjugation `x ↦ g⁻¹ x g` is `C.pointwiseFixer Y`. This is Mathlib's
  `SubMulAction.fixingSubgroup_map_conj_eq` together with `g⁻¹ · (g · Y) = Y`.
* `UnramifiedCompatibleModelKernelStatement.{u}` (a `Prop`): the host statement
  with two changes. First, the sets are `C.apartmentMap '' Ωa` and
  `C.apartmentMap '' Ωa'` (no translation by `g`). Second, it assumes
  `(torusCentralizer C.i).IsRepresentedBy E.i`. The other hypotheses are those
  of the host: `Ωa` is nonempty; every affine function `C.Apartment → ℝ` is
  bounded above on `Ωa'`; `Ωa` lies in the closure of `Ωa'` for the topology
  induced by affine functions; `N` and `N'` are smooth integral models of `G_K`
  over the integers of `K` with integral points
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa)` and
  `E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa')`. The conclusion is
  the host conclusion: for every model homomorphism `ψ : N'.Hom N (𝟙 _)`, the
  kernel of `ψ.specialFibreMap` is smooth, connected and unipotent.
* `integralPoints_transport_innerIso hind C E E' g Y M hM`: let `M` be an
  integral model of `G_K` with integral points
  `E.zeroPoints ⊓ C.pointwiseFixer (g · C.apartmentMap '' Y)`. Transport `M`
  along the inner automorphism `Int(g⁻¹)` of `G_K`, using the published
  `IntegralModel.transport` (same integral group scheme, generic identification
  composed with `Int(g⁻¹)`). The transported model has integral points
  `E'.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Y)` for any second zero
  datum `E'`.

  *Proof.* The published `transport_integralPoints` says the new integral
  points are the image of the old ones under the rational-point map of
  `Int(g⁻¹)`. This map is injective (`rationalPoints_map_injective_of_iso`), so
  it commutes with intersections (`Subgroup.map_inf_eq`). By the published
  `zeroPoints_transport`, the image of `E.zeroPoints` is the zero subgroup of the
  transported datum `E.transport Int(g⁻¹)`. That equals `E'.zeroPoints` by
  `hind`. By the published `rationalPoints_map_innerIso`, the rational-point map
  is conjugation by `g⁻¹`. So the fixer image is computed by
  `pointwiseFixer_smul_image_map_conj`.
* `kernel_transportId_iff ψ e` (`Iff.rfl`): the published
  `Hom.transportId` carries `ψ : N'.Hom N (𝟙 _)` to a homomorphism of the
  transported models with the same integral morphism. Its special-fibre map is
  literally `ψ.specialFibreMap`, so the kernel conclusions are the same
  proposition.

## The reduction theorem

* `unramifiedModelKernel_of_compatible hquasi hind hcore`: from
  `hquasi : UnramifiedQuasiSplitStatement.{u}`,
  `hind : UnramifiedZeroPointsIndependenceStatement.{u}` and
  `hcore : UnramifiedCompatibleModelKernelStatement.{u}`, it concludes
  `UnramifiedModelKernelStatement.{u}`.

  *Proof.* Take the host data `F, G, C, E, g, Ωa, Ωa', N, N', ψ`. The group
  `G_K` is connected reductive (a field of `C`), hence quasi-split by `hquasi`.
  Apply `exists_isRepresentedBy_torusCentralizer` to the maximal split torus
  `C.i` to get a compatible zero datum `E'`. Transport `N` and `N'` along
  `Int(g⁻¹)`. They stay smooth, since smoothness concerns only the unchanged
integral group scheme (the hypotheses `hN`, `hN'` are reused as they are; compare
the published `isSmooth_transport_iff`, which is `Iff.rfl`). By
  `integralPoints_transport_innerIso` their integral points are
  `E'.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa)` and the same with
  `Ωa'`. Apply `hcore` to `E'`, the transported models and `ψ.transportId`.
  Then `kernel_transportId_iff` returns the conclusion for `ψ`.

The theorems `integralPoints_transport_innerIso` and
`unramifiedModelKernel_of_compatible` raise `maxHeartbeats` to 1600000, a
finite limit, because elaborating the transported models is slow.
