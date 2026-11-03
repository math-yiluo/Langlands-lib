# The same torus and compact intersection in the actual standard Levi

Worker 1229, task `219b673d-b7f3-47fb-9019-d1642687d4ac`.

This internal definition adapter uses the actual closed standard Levi
representative already constructed in
`Langlands.GroupScheme.Rational.StandardRepresentability`.
It identifies the subgroup of its rational points whose image is the
intersection with the same chosen geometric `K₀`.

## Provenance

The construction is derived entirely from published Library definitions and
lemmas: `Standard.leviScheme`, `Standard.leviHom`,
`Standard.isRepresentedBy_leviHom`, `Standard.isClosedSubgroup_leviHom`,
`SubgroupFunctor.IsRepresentedBy.factorHom`,
`range_le_torusCentralizer`, `torusCentralizer_le_standardLevi`,
`IsMaximalSplitTorus.isMaximalSplitTorus_factorHom`, and
`standardLeviRationalPointsEquiv`.
The chosen subgroup is `KPApartmentData.specialCompactSubgroup` from the
paired `SpecialCompact` module.

No new external structural theorem is imported or asserted. The adapter
provides definitions needed for the standard-Levi inheritance requested in
Renard S19(5), as mapped in
`notes/renard/chapter-v-structural-inputs.md`. It supplies no inherited
apartment, minimal-parabolic comparison, compactness or maximality conclusion.

## Exact declarations

For any field `F`, affine group scheme `G`, commutative group scheme `S`,
homomorphism `i : S.toGrp ⟶ G`, cocharacter `ν`, and character subset `J`,
the declarations in namespace `Langlands.GroupScheme.Standard` are:

- `leviTorusHom i ν J : S.toGrp ⟶ Standard.leviScheme i ν J`.
  The range of `i` centralizes itself on every test scheme, hence lies in
  the same choice-free standard Levi functor. Its all-test representative
  gives the factorization through the specific `Standard.leviHom i ν J`.
- `leviTorusHom_comp` states that composing this factor with the inclusion
  is exactly `i`.
- `isMaximalSplitTorus_leviTorusHom` says that `IsMaximalSplitTorus i`
  implies maximal splitness of this factor. The proof applies the existing
  maximal-split-torus descent lemma to the closed represented subgroup.
  It needs no separate reductivity hypothesis.
- `leviPointsEquiv i ν J` identifies the rational points of this specific
  scheme with the actual subgroup `standardLeviPoints i ν J`.
  It specializes the existing rational-point comparison.
  `leviPointsEquiv_val` identifies its underlying ambient point with
  `rationalPoints.map (Standard.leviHom i ν J)`.

Now let `F` be a full nonarchimedean local field, assume the monomorphism
needed by `KPApartmentData`, and fix
`D : KPApartmentData i (localFieldOrder F)` and `x : D.Apartment`.
In namespace `Langlands.Geometry.Building.KPApartmentData`:

- `D.specialCompactLeviSubgroup ν J x` is the preimage of
  `D.specialCompactSubgroup x` under the rational-point homomorphism of
  the specific inclusion `Standard.leviHom i ν J`.
  It is a subgroup of the rational points of `Standard.leviScheme i ν J`.
- `mem_specialCompactLeviSubgroup` unfolds its membership condition.
- `specialCompactLeviSubgroup_map` proves that its image in the original
  `G(F)` is exactly
  `D.specialCompactSubgroup x ⊓ standardLeviPoints i ν J`.
  In the forward direction the rational-point equivalence puts every
  image in the actual Levi subgroup. In the reverse direction its
  surjectivity lifts an element of the intersection; that lift belongs to
  the preimage by definition.

## Scope retained

These algebraic adapters make sense for every `J`, with the same `D` and `x`.
For the structural standard-Levi targets, `J` will be a subset of
`simpleRelativeRoots i ν`, `ν` will be generic, `i` maximal split, and
`G` connected reductive. The definitions do not assume or prove those
structural specializations. They preserve the empty-indexing convention
of the published choice-free standard subgroup functors.

This fixes the group scheme, torus map, ambient inclusion and compact
intersection to use in a future inherited-apartment comparison. It does
not construct corrected root-valuation data for the Levi or a map of
apartments, identify its minimal parabolic with the ambient intersection,
or show that this subgroup is a special maximal compact-open subgroup.
Those remain independent obligations of the full task. No equality of
parahoric, `K₀` and full reduced fixer is imposed.
