# Base change of the actual full rigidified universal property

`RigidifiedUniversalBaseChangeStatement` states the following. Take a
morphism of schemes `b : S' → S`, an abelian scheme `A/S`, an `S`-scheme
`P` and an actual rigidified family `L` on `P ×_S A`. Suppose `L` is
universal for all rigidified line bundles. Then the explicitly
base-changed family `(baseChangeFamily b A P).obj L` is universal for all
rigidified line bundles relative to `A_{S'} = (baseChange b).obj A`. Its
parameter scheme is the actual slice pullback `(Over.pullback b).obj P`,
which is the fibre product `P_{S'} = P ×_S S'`. All schemes lie in one
universe `u`. Nothing is assumed about `S`, `S'`, `b`, `A` or `P` beyond
these data: there is no field, finiteness, noetherian, reducedness or
quasi-separatedness hypothesis.

## Meaning of the hypothesis and conclusion

Both occurrences of `RigidifiedLineBundle.IsUniversal` are the existing
Library predicate, applied to the structure morphism of the abelian
scheme, its unit section `unitSection` and the section equation
`unitSection_comp`. By the published `isUniversal_iff`, the hypothesis
says: for every `S`-scheme `T` and every actual rigidified line bundle `M`
on `T ×_S A`, rigidified along the unit section, there is a unique
`S`-map `h : T → P` with `h*L` isomorphic to `M` as rigidified line
bundles. The conclusion says the same for every `S'`-scheme `T`, every
rigidified line bundle on `T ×_{S'} A_{S'}`, rigidified along the unit
section of `A_{S'}`, and `S'`-maps `T → P_{S'}`. Uniqueness concerns the
classifying map, not the bundle isomorphism.

Every rigidified family is classified, not only Picard-zero families, and
every test scheme is allowed, including nonreduced ones. This differs from
the published `PicardZeroUniversalBaseChangeStatement`. That statement
uses `IsUniversalPicardZero`, which adds a geometric fibre condition and
classifies only Picard-zero families. It does not state this result.

## The base-changed family

The new family is the existing explicit construction `baseChangeFamily`
from `PoincareBaseChange`. It is not new data. It first pulls `L` back in
the parameter along `baseChangeParameterMap b P : P_{S'} → P`, viewed over
`S`. Then `familyBaseChange` changes the ground base along the canonical
comparison `P_{S'} ×_{S'} A_{S'} → P_{S'} ×_S A`. Both steps keep the
rigidification through the existing rigidified pullback functors. The
unit section of `A_{S'}` is compatible with the original unit section
(`unitSection_baseChange_fst` and `relativeSection_familyBaseChangeSpaceMap`
in `FamilyBaseChange`).

The hypothesis assumes only that the given `L` is universal. The statement
asserts no existence of a universal family, representing scheme, Picard
scheme or dual abelian scheme. It also says nothing about the geometry of
`P` or `P_{S'}`.

This file states a theorem obligation as a `Prop`-valued definition. It
contains no proof of that obligation.

## Provenance and proof obligations

This is a derived statement about the existing Library universal property.
Edixhoven–van der Geer–Moonen, *Abelian Varieties* (preliminary version),
Chapter VI §1, (6.2), printed p.88 (PDF p.92), defines the rigidified
functor `P_{X/S,ε}` on `S`-schemes. In the same paragraph it formulates the
universal property of the Poincaré bundle on `X ×_S P_{X/S,ε}`: every
rigidified line bundle on `X ×_S T` is isomorphic to `(id_X × g)*` of the
Poincaré bundle for a unique `g : T → P_{X/S,ε}`. The retained source is
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That passage motivates the universal property. It does not explicitly state
the base-change theorem formalized here. The source writes `X ×_S T` and
an isomorphism from the given bundle to the pullback. The Library uses the
parameter-first product `T ×_S X` and an isomorphism from the pullback to
the given bundle. Neither difference changes which classes are classified,
since the products are canonically isomorphic and isomorphisms invert.
The source's standing hypotheses (∗) in (6.2) are not needed to formulate
this transport statement, and they do not appear in it.

The statement rests on two categorical identifications for an
`S'`-scheme `T`. First, `T ×_{S'} A_{S'} ≅ T ×_S A` compatibly with the
unit sections, so the published `familyBaseChangeEquivalence` makes
rigidified families relative to `A_{S'}` over `T` equivalent to rigidified
families relative to `A` over `T` viewed as an `S`-scheme. Second,
`S'`-maps `T → P_{S'}` correspond to `S`-maps `T → P`. The published
`baseChangeFamilyPullbackIso` relates these identifications to the explicit
family `baseChangeFamily`. The expected proof is the classification-transport
part of the private lemma `universalBaseChange_of_geometric` in the
published module `PicardZeroUniversalBaseChangeProof`, without its
Picard-zero membership conditions. It would use these published
constructions:

- `familyBaseChangeInverse`, `familyBaseChangeUnitIso` and
  `familyBaseChangeCounitIso` from `FamilyBaseChangeEquivalence`, which
  move a new family back to the old base and compare the round trips;
- `baseChangeParameterEquiv`, the slice pullback adjunction, and
  `baseChangeFamilyPullbackIso` from `FamilyBaseChangeNaturality`, which
  compares pullback of the explicit new family with ground-base change of
  the old pullback;
- `RigidifiedLineBundle.isUniversal_iff` from `RigidifiedUniversalBundle`.

In this route, a new family over `T` is transported to the old base. The
old universal property classifies it uniquely, and the adjunction and
family comparisons give existence and uniqueness of the new classifying
map. Assembling the published comparisons into the conclusion is the
separate proof obligation; this module proves nothing.
