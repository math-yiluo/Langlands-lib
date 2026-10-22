# The smooth-part functor and enough injectives

Author: Worker 13.

This module makes the published smooth part of an algebraic representation
into a functor to the published category `Langlands.SmoothRep R G`, proves
that it is right adjoint to the inclusion `toRep`, and deduces that the
smooth category has enough injectives.

## Mathematical content

Let `R` be a commutative ring and `G` a topological group. In the section
`Functor` the ring, group and carrier universes are independent.

- `smoothPartObj R G A` is the smooth part `smoothPart A.ρ` of an algebraic
  representation `A`, on the submodule `smoothVectors A.ρ` of vectors fixed
  by some open subgroup, bundled with the published proof
  `isSmooth_smoothPart`.
- `smoothPartFunctor R G : Rep R G ⥤ SmoothRep R G` sends an intertwiner to
  its restriction `smoothMap` to smooth vectors. Identity and composition
  laws hold by definition. `smoothPartFunctor_map_apply` records that the
  restricted map is the original map on the underlying vector.
- `toRepSmoothPartAdjunction R G : toRep ⊣ smoothPartFunctor R G`. The hom
  equivalence sends an intertwiner `f : toRep A ⟶ B` from a smooth
  representation `A` to its codomain restriction `smoothLift`, which lands in
  the smooth vectors because the image of a vector fixed by an open subgroup
  is fixed by the same subgroup. The inverse composes with the inclusion of
  smooth vectors. Both round trips and the naturality laws hold by
  definition. `toRepSmoothPartAdjunction_homEquiv_apply` and
  `toRepSmoothPartAdjunction_counit_app_apply` record the hom equivalence and
  that the counit is the inclusion of smooth vectors.
- `injective_smoothPart`: the smooth part of an injective algebraic
  representation is injective in the smooth category. This is Mathlib's
  `Adjunction.map_injective`, using that the left adjoint `toRep` preserves
  monomorphisms (companion module `Category/Abelian`).

In the section `EnoughInjectives`, `R` and `G` lie in one universe `u` and the
representation carriers lie in the same universe:

- `rep_enoughInjectives : EnoughInjectives (Rep.{u} R G)` transports
  Mathlib's enough injectives for modules over the group algebra `R[G]`
  through Mathlib's equivalence `Rep.equivalenceModuleMonoidAlgebra`. That
  This module proves the instance in that single-universe setting; this is a
  restriction of the interface here, not of Mathlib's equivalence.
- `enoughInjectives : EnoughInjectives (SmoothRep.{u, u, u} R G)` follows by
  Mathlib's `EnoughInjectives.of_adjunction`: embed `toRep A` into an
  injective algebraic representation `I`; its adjoint transpose embeds `A`
  into the smooth part of `I`, which is injective.

No enough-projectives claim is made. Smooth representations with torsion
coefficients need not have enough projectives in general.

## Sources and provenance

Bernstein and Zelevinsky, *Representations of the group GL(n,F) where F is a
non-Archimedean local field*, Russian Math. Surveys 31:3 (1976), Chapter I,
Definition 2.1(a), printed p.15 (PDF page 15), defines the algebraic part
`E^a` of a representation, the vectors with open stabilizer, and notes that
it is a subrepresentation. This is the published `smoothPart`. Worker 13
read that passage. Registered source
`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), printed p.309, Proposition 4.4, takes Ext
as the derived functor of Hom in the category of smooth coefficient
representations, which requires enough injectives or projectives. Worker 13
read this passage. Registered source
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

The adjunction and the enough-injectives argument are internal derived
infrastructure: the standard argument that a right adjoint of a
monomorphism-preserving functor preserves injectives. The general ring and
topological-group scope is a domain of definition only. The proofs use the
published smooth-part constructions, the companion `Category/Abelian`, and
Mathlib at commit `5ed2965256430c3649e86755f9576b54eca72435`. The imports
were checked in Library commit `f01c1864161b6d1cdc1d04b1f8d577dfd4e8400f`.
