# The abelian category of smooth representations

Author: Worker 13.

This module proves that the published full subcategory
`Langlands.SmoothRep R G` of Mathlib's `Rep R G`, from
`Langlands.Representation.Category.Basic`, is an abelian category. The
category, its objects, morphisms and its preadditive and linear structures are
reused unchanged. Only closure properties of the published predicate
`smoothRepProperty R G` are proved here.

## Mathematical content

Let `R` be a commutative ring and `G` a group with a topology. The ring, group
and representation-carrier universes are independent. No continuity of the
group operations is assumed.

- `rep_limit_ext` is a helper: two elements of a limit of algebraic
  representations agree if all their projections agree. It transports
  Mathlib's concrete limit extensionality through the forgetful functor to
  modules.
- `smoothRepProperty_containsZero`: the zero representation is smooth, since
  its only vector is zero and zero is a smooth vector.
- `smoothRepProperty_isClosedUnderSubobjects`: if `f : X ⟶ Y` is a
  monomorphism of algebraic representations and `Y` is smooth, then `X` is
  smooth. Monomorphisms in `Rep` are injective intertwiners, and the published
  transfer `isSmooth_of_injective` applies.
- `smoothRepProperty_isClosedUnderQuotients`: dually, epimorphisms in `Rep`
  are surjective, and `isSmooth_of_surjective` applies.
- `smoothRepProperty_isClosedUnderBinaryProducts`: a vector of a binary
  product is fixed by the intersection of open subgroups fixing its two
  projections. That intersection is open, and `rep_limit_ext` gives the
  fixing equation.
- `smoothRepProperty_isClosedUnderFiniteProducts` follows from the binary
  case and the zero case by Mathlib's `IsClosedUnderFiniteProducts.mk'`.
- `abelian : Abelian (SmoothRep R G)` is then Mathlib's theorem in
  `CategoryTheory/Abelian/Subcategory.lean`: a full subcategory of an abelian
  category that contains zero and is closed under kernels, cokernels and
  finite products is abelian. Kernels and cokernels are closed because
  subobjects and quotients are.
- `toRep_preservesMonomorphisms` and `toRep_preservesEpimorphisms`: the
  inclusion `toRep` preserves monomorphisms and epimorphisms, by the companion
  Mathlib lemmas for such subcategories, which use that the inclusion
  preserves kernels and cokernels. No separate exactness instance is declared.
- `mono_iff_injective` and `epi_iff_surjective`: a morphism of smooth
  representations is a monomorphism exactly when the underlying linear map is
  injective, and an epimorphism exactly when it is surjective.

Kernels, cokernels and finite products are those of algebraic representations,
computed on underlying modules. Infinite products are not claimed to stay
smooth; in general they do not.

## Sources and provenance

Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys 31:3 (1976), Chapter I,
Definition 2.1, printed p.15 (PDF page 15), defines the category `Alg G` of
algebraic (smooth) representations with intertwining operators. Worker 13
read that passage. Registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed p.309, Proposition 4.4, takes Ext
as the derived functor of Hom in the category of smooth coefficient
representations. This presupposes an abelian structure. Printed p.316 calls
these categories of smooth representations abelian. Worker 13 read both
passages. Registered source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The closure proofs are internal derived infrastructure. The sources work over
complex or torsion coefficients and locally profinite groups; the general
ring, topology and universe scope here is a domain of definition only. The
proofs use only the published smoothness transfers and Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`. The imports were checked in
Library commit `f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f`.
