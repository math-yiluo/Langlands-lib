# Identity components of smooth affine group schemes over a field

This file constructs the identity component `H⁰` of a smooth affine group scheme
`H` over an arbitrary field `k`. It also constructs the inclusion `H⁰ ⟶ H` as a
group-scheme homomorphism and proves the following laws: open and closed
immersion, range, smoothness, affineness, connectedness, irreducibility,
geometric connectedness and geometric irreducibility, all-test normality, the
universal property for connected sources, and compatibility with field
extension. `H⁰` is the open subscheme of `H` on the connected component of the
identity point, with the restriction of the group law of `H`. It is constructed
here, not supplied by a hypothesis or by an existence assumption.

## Source

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Definition A.1.10, printed p.469 (PDF p.495). The source is registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`. The source
defines the identity component `H⁰` of a group scheme `H` locally of finite type
over a field `k` as the unique connected open and closed subscheme of `H` that
contains the identity point. It states, citing SGA3 VI_A 2.3.1 and 2.4, that
`H⁰` is a geometrically irreducible normal subgroup scheme of finite type, so
its formation commutes with any extension of the ground field.

The Lean development covers the smooth affine case of this definition. Here is
how each source assertion corresponds to the Lean:

- "Connected open and closed subscheme containing the identity point":
  `identityOpen H` is the open subscheme on `connectedComponent (identityPoint H)`.
  The inclusion is an open immersion and a closed immersion, its range is that
  connected component (`range_identityComponentι`), and `H⁰` is connected.
- "Unique": a connected group scheme `P` with a homomorphism `j : P ⟶ H` that is
  an open and a closed immersion has range equal to the identity component
  (`range_eq_identitySet`). It is canonically isomorphic to `H⁰` over `H`
  (`isoOfIsOpenImmersion`). This uniqueness is stated for subgroups, not for
  arbitrary subschemes.
- "Normal subgroup scheme": `isNormal_range_identityComponentι`, with the
  all-test meaning of `SubgroupFunctor.IsNormal`.
- "Geometrically irreducible": the instance
  `geometricallyIrreducible_identityComponent` for the structure morphism of
  `H⁰`, together with `irreducibleSpace_identityComponent` (the underlying
  space of `H⁰` is irreducible) and `geometricallyConnected_identityComponent`.
  Finite type is not stated separately: it follows from smoothness and
  affineness over a field but is not recorded.
- "Formation commutes with extension of the ground field": `baseChangeIso` and
  its compatibility with the two inclusions.

## Hypotheses and universe scope

Throughout, `k : Type u` is an arbitrary field and
`H : GroupScheme (Spec (CommRingCat.of k))` is an actual group scheme, that is
`Grp (Over (Spec k))`. Every declaration about `H` from the geometric input
`exists_isOpenImmersion_geometricallyConnected` onward assumes
`[Smooth H.X.hom]` and `[IsAffineHom H.X.hom]`; the one exception is
`range_eq_identitySet`, which does not use them. The two declarations in that
part that do not involve `H`, `connectedSpace_splitTorus` and `specMap`, have
neither hypothesis. There is no hypothesis on
perfectness, characteristic, reductivity, rational points, or existence of an
identity component. The two hypotheses give the local finite type and
quasi-compactness needed by the geometric input below, the flatness behind the
universal openness of the structure morphism of `H⁰`, and smoothness and
affineness of `H⁰` and of the base change of `H`. CGP's general case of group
schemes that are only locally of finite type is not formalized here.

The universe `u` is arbitrary but is a single universe. The field, all schemes
(`Scheme.{u}`) and all test schemes live in it. In the base-change section
`L : Type u` is a field in the same universe as `k`, and `φ : k →+* L` is an
arbitrary ring homomorphism, which is a field embedding. Base change is the
existing `GroupScheme.baseChange` along the induced morphism
`specMap φ = Spec.map (CommRingCat.ofHom φ) : Spec L ⟶ Spec k`.
Field extensions with `L` in a different universe from `k` are not covered.

## The identity point and the geometric input

`basePoint k` is `IsLocalRing.closedPoint k`, the unique point of `Spec k`. It
is regarded as a point of the monoidal unit of `Over (Spec k)`.
`identityPoint H` is the image of this point under the unit section
`η[H.X].left`, and `identitySet H` is its connected component.
`unit_left_apply` records that the unit section sends every point of `Spec k`
to the identity point.

`range_subset_identitySet` is the basic topological lemma. Let `g : P ⟶ H.X` be
a morphism over `k` from a connected scheme `P`, and suppose some `k`-point `a`
of `P` satisfies `a ≫ g = η[H.X]`. Then the range of `g` lies in `identitySet H`,
because the range of `g` is connected and contains the identity point.

`exists_isOpenImmersion_geometricallyConnected` is the only geometric input. It
applies the published theorem
`GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`
to the group law of `H`, converted by `GoodReductionJacobian.relativeGroupLawOfGrpObj`.
That theorem is ported from the Anthropic FLT formalization and requires only
local finite type and quasi-compactness over the field. The result is a scheme
`G₀` and a morphism `i : G₀ ⟶ H.X.left` with these properties:

- `i` is an open and a closed immersion;
- `i ≫ H.X.hom` is geometrically irreducible and geometrically connected;
- the range of `i` is `identitySet H`.

The ported theorem also returns `IrreducibleSpace G₀`, a group law on `G₀`, and
further facts; these are discarded.

The unit point of the converted group law is identified with `identityPoint H`
through `relativeGroupLawOfGrpObj_one` and `unit_left_apply`.

`H⁰` is not defined as the scheme `G₀`, which is chosen non-canonically by the
existential. The construction uses `G₀` for two facts only. First, `identitySet H`
is open and closed (`isClopen_identitySet`). Second, geometric irreducibility
and geometric connectedness of `G₀` transfer to the canonical open subscheme.
The transfer is `of_range_eq`: if `P` is a property of morphisms of schemes that
respects isomorphisms, and `P (i ≫ H.X.hom)` holds for some open immersion `i`
with range `identitySet H`, then `P` holds for the structure morphism of the
open subscheme. Its proof uses `IsOpenImmersion.isoOfRangeEq`, which identifies
the source of `i` with that open subscheme over `H`. `GeometricallyIrreducible`
and `GeometricallyConnected` respect isomorphisms because they are stable under
base change.

## The scheme `H⁰`

- `identityOpen H : H.X.left.Opens` is the open set `identitySet H`.
- `identityComponentOver H` is `Over.mk ((identityOpen H).ι ≫ H.X.hom)`, the
  open subscheme as a scheme over `k`. `inclusionOver H` is the inclusion
  `Over.homMk (identityOpen H).ι`.
- The inclusion is an open immersion. It is also a closed immersion: an open
  immersion is a preimmersion, and its range is closed
  (`IsClosedImmersion.of_isPreimmersion`).
- `H⁰` is connected because it is homeomorphic to a connected component.
- It is geometrically irreducible and geometrically connected by the transfer
  above. It is irreducible because it is geometrically irreducible over the
  one-point space `Spec k`
  (`GeometricallyIrreducible.irreducibleSpace_of_subsingleton`).
- It is smooth and affine over `k`, because the structure morphism is an open
  and closed immersion followed by the smooth affine structure morphism of `H`.
- Its structure morphism is universally open (`UniversallyOpen.of_flat`).
  Together with geometric connectedness, Mathlib then gives connectedness of
  the fiber product `H⁰ ×_k H⁰`.

## The restricted group law

All three operations are restrictions of the operations of `H`, built as actual
scheme morphisms over `k` with `FiniteEtaleImage.liftOver`. This is
factorization through an open immersion over the base, applied once the range
is known to lie in `identitySet H`.

- `one`: the unit section of `H` factors through `H⁰` (`one_range_subset`),
  since `Spec k` is connected.
- `mul`: the composite `H⁰ ×_k H⁰ ⟶ H ×_k H ⟶ H` factors through `H⁰`
  (`mul_range_subset`). The source is connected and the `k`-point
  `(one, one)` maps to the identity.
- `inv`: the composite `H⁰ ⟶ H ⟶ H` of the inclusion with inversion factors
  through `H⁰` (`inv_range_subset`). The source is connected and `one` maps to
  the identity, since `1⁻¹ = 1`.

`one_fac`, `mul_fac` and `inv_fac` state that these operations are compatible
with the inclusion. The group-object structure `grpObj_identityComponentOver` is
`GroupObjectDescent.grpObjOfMono` applied to the monomorphism `inclusionOver H`.
It keeps the three operations definitionally and proves the group axioms by
cancelling the inclusion. The inclusion is a monoid homomorphism for this
structure.

`Langlands.GroupScheme.identityComponent H` is the resulting group scheme over
`Spec k`. The lemmas `one_identityComponent`, `mul_identityComponent` and
`inv_identityComponent` hold by `rfl`: the unit, multiplication and inverse of
`identityComponent H` are `one H`, `mul H` and `inv H`.
`Langlands.GroupScheme.identityComponentι H : identityComponent H ⟶ H` is the
inclusion as a group-scheme homomorphism. Its proved laws:

- `isOpenImmersion_identityComponentι` and `isClosedImmersion_identityComponentι`:
  its underlying scheme map is an open immersion and a closed immersion. Also
  `isClosedSubgroup_identityComponentι`;
- `range_identityComponentι`: the topological range of the underlying map is
  `connectedComponent (identityPoint H)`;
- `smooth_identityComponent`, `isAffineHom_identityComponent`,
  `geometricallyIrreducible_identityComponent` and
  `geometricallyConnected_identityComponent`: the structure morphism of
  `identityComponent H` is smooth, affine, geometrically irreducible and
  geometrically connected. `connectedSpace_identityComponent` and
  `irreducibleSpace_identityComponent`: its underlying space is connected and
  irreducible;
- `mono_identityComponentι`: the inclusion is a monomorphism of group schemes.

## Normality

`conjOver H : H ×_k H⁰ ⟶ H` is the morphism `(g, y) ↦ g y g⁻¹`, built from
Mathlib's `GrpObj.conj`. `lift_conjOver` computes it on points.
`range_conjOver_subset` shows that its range lies in `identitySet H`. Let
`p : H ×_k H⁰ ⟶ H` be the first projection. It is geometrically connected
because it is a base change of the structure morphism of `H⁰`, so each fiber of
`p` is connected. Each fiber `p⁻¹{p z}` contains the point `s(p z)` of the
section `s = (𝟙, e)`, and `s ≫ conjOver H` is the unit, so `s(p z)` maps to the
identity point. The image of the fiber is therefore a connected set containing
the identity point, and `z` lies in the fiber.

`isNormal_range_identityComponentι` states that the range subgroup functor
`SubgroupFunctor.range (identityComponentι H)` is normal in the all-test sense
of `SubgroupFunctor.IsNormal`. For every test scheme `T` over `k`, every point
`g : T ⟶ H.X`, and every point `x` factoring through `H⁰`, the point
`g * x * g⁻¹` factors through `H⁰`. If `x = y ≫ ι`, the factorization is the
lift of `lift g y ≫ conjOver H` through the open immersion.

## Factorization of homomorphisms from connected group schemes

Let `K` be a group scheme over `k` with `ConnectedSpace K.X.left`, and let
`f : K ⟶ H` be a homomorphism. The range of `f` lies in the identity component
(`range_subset_range_identityComponentι`), because `f` preserves the unit.

- `factor H f : K ⟶ identityComponent H` is the factorization through the open
  immersion. It is a group-scheme homomorphism, constructed by the generic
  `liftHom`: the lift of a homomorphism through an open-immersion homomorphism
  is a monoid homomorphism, checked by cancelling the inclusion.
- `factor_identityComponentι` proves `factor H f ≫ identityComponentι H = f`.
- `eq_factor` and `existsUnique_factor` prove uniqueness. Homomorphisms into a
  group scheme through an open-immersion homomorphism are determined by their
  composites (`hom_ext_of_isOpenImmersion`).
- `homEquiv` packages this as a bijection
  `(K ⟶ identityComponent H) ≃ (K ⟶ H)` for connected `K`.

Split tori are connected (`IsSplitTorus.connectedSpace`). The instance
`connectedSpace_splitTorus` makes the factorization apply directly to the actual
split torus `splitTorus (Spec k) I` for any finite `I : Type u`.
`existsUnique_factor_of_isSplitTorus` applies it to any group scheme `T` with
`IsSplitTorus T`.

## Characterization and base change

Let `P` be a connected group scheme over `k`, and let `j : P ⟶ H` be a
homomorphism whose underlying scheme map is an open and a closed immersion.
`range_eq_identitySet` shows that the range of `j` is `identitySet H`: the range
is clopen, connected, and contains the identity point.
`isoOfIsOpenImmersion H j : P ≅ identityComponent H` is then the isomorphism of
group schemes whose maps are `factor H j` and the lift of `identityComponentι H`
through `j`. The lemmas `isoOfIsOpenImmersion_hom_identityComponentι` and
`isoOfIsOpenImmersion_inv_comp` state its compatibility with the inclusions.

For the field extension, write `H_L` for `(GroupScheme.baseChange (specMap φ)).obj H`.
`H_L` is smooth and affine over `L`, since both properties are stable under base
change. The base change of the inclusion,
`(GroupScheme.baseChange (specMap φ)).map (identityComponentι H)`, is again an
open and a closed immersion (`MorphismProperty.overPullbackMap`). The base change
of `H⁰` is connected because `H⁰` is geometrically connected over `k` and
`Spec L` is a single point (`GeometricallyConnected.connectedSpace_of_subsingleton`).

`baseChangeIso H φ` applies the characterization to this base-changed inclusion
into `H_L`. It is the comparison isomorphism of group schemes over `Spec L`
between the base change of `H⁰` and `identityComponent H_L`:

- `baseChangeIso_hom_identityComponentι` proves that `(baseChangeIso H φ).hom`
  followed by the inclusion of the identity component of `H_L` equals the base
  change of `identityComponentι H`;
- `baseChangeIso_inv_comp` proves the inverse form: `(baseChangeIso H φ).inv`
  followed by the base change of `identityComponentι H` equals the inclusion of
  the identity component of `H_L`.

So the two inclusions into `H_L` agree.

## Reused constructions

- `FiniteEtaleImage.liftOver` (Library): factorization over the base through
  an open immersion, built on Mathlib's `IsOpenImmersion.lift`.
- `GroupObjectDescent.grpObjOfMono` and `isMonHom_grpObjOfMono` (Library):
  restriction of a group object along a monomorphism with specified
  operations.
- `GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent`
  and `relativeGroupLawOfGrpObj` (Library, ported from the Anthropic FLT
  formalization): openness, geometric irreducibility and geometric
  connectedness of the identity component.
- `IsSplitTorus.connectedSpace` (Library) and Mathlib's `GeometricallyConnected`,
  `GeometricallyIrreducible`, `UniversallyOpen.of_flat` and
  `IsOpenImmersion.isoOfRangeEq`.
