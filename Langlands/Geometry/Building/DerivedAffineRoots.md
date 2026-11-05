# Actual affine roots and Weyl groups under derived pullback

Use the supplied structural data of `DerivedApartment`: a field
`k : Type u`, an actual derived inclusion `d : D → G`, affine locally
finite-type `D`, affine smooth `G`, split tori `T`, `A`, `S`, monomorphic
embeddings `j`, `i` with `i` maximal split, and the square
`j ≫ d = e ≫ i`. The actual product of `e : T → S` and `c : A → S` is flat
and surjective as a scheme map, and `c ≫ i` is central on every test scheme.
Let `P : KPApartmentData i ω` be an actual ambient apartment class for any
scalar valuation function `ω : kˣ → ℝ`.

`affineFunctionalDerivedPullbackEquiv` is inverse precomposition by the
actual point affine equivalence constructed in `DerivedApartment`. It is a
real-linear equivalence on affine functionals. Evaluation at a pulled-back
point equals the original value, its derivative composes with the original
`derivedTranslationEquiv`, and it preserves addition of the same real
constant on both apartments.

The root-form identity for `derivedTranslationEquiv` proves that a
functional's derivative is an actual ambient root form exactly when its
transport has the corresponding actual source root form.

The filtration identity of `DerivedFunctions` gives an exact restricted
inverse-image formula for each original affine root group: a source point
belongs precisely when it is in the corresponding source root subgroup and
its literal image under `d` belongs to the ambient affine root group.
Quantifying over all apartment points is valid because the actual point
pullback is bijective. The same formula holds for strict affine root groups,
using preservation of positive constant shifts.

`map_affineRootGroup_derivedPullback` and
`map_affineRootGroupPlus_derivedPullback` prove equality of the original
ambient groups with these source groups' images. Surjectivity takes place
inside the corresponding actual root subgroup, using
`derivedRootGroupPointsEquiv`.

For an actual ambient root `a`, the character `2a` vanishes on the central
complement. `derivedRoot_mem_iff_of_central_vanishing` therefore detects the
existence of the double root after restriction to `T`. If it exists, the
actual root-point equivalence supplies its exact image; otherwise both
`doubleRootGroupPoints` use their defined trivial-subgroup convention.
This proves `map_doubleRootGroupPoints_derivedPullback`.

The ordinary affine-root noncontainment test is also reflected. Both the
strict affine root group times the double-root group and the non-strict
affine root group lie in one source root subgroup. The original point map
is injective there, so its exact images detect the required containment.
The extended affine-root test, inequality of the strict and non-strict
groups, is reflected by the same injectivity and image equalities.

Consequently the module proves preservation and reflection of both the
ordinary and extended affine-root predicates.
`affineRootsDerivedPullbackEquiv` and
`extendedAffineRootsDerivedPullbackEquiv` restrict the actual functional
equivalence to those root subtypes. In particular,
`transportedRoots_derivedPullback` identifies the transported ordinary root
set with the actual derived root set, and
`map_affineWeylGroup_derivedPullback` identifies the original affine Weyl
groups under conjugation by the actual apartment affine equivalence.

This internal proof adapts `CentralIsogenyAffineRoots` with the actual
derived-root bijection, original derived point map and reduced cocharacter
equivalence. The double-root comparison uses central character vanishing,
not an isogeny hypothesis on `e`. No additional external theorem is invoked.
The structural tori remain supplied. No source root-system axiom, full
centralizer datum, opposite-pair existence, or final normalizer image
equality is asserted by this module.
