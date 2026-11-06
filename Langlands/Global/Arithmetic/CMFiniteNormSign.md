# Finite local norms and signs in CM extensions

This helper for the CM half-weight character construction develops the
norm and sign calculation used in Harris–Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties*, proof of Corollary VII.2.8, printed
pp. 244–245. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`.

`IsFiniteLocalNorm (E := E) a` means that at every finite place `v` of `F`,
there is a place `w` of `E` above `v` and a unit of the field `E_w` whose actual
field norm is the diagonal image of `a : Fˣ`. Here a unit is an arbitrary
nonzero field element, with no integrality condition.

`finiteLocalInvariant_cyclicClass_eq_zero_of_norm` identifies the restriction of a global cyclic carry class
with the carry class at a completion. An actual local norm makes that class
zero by the cyclic norm criterion for an injective cyclic character, so its
local invariant vanishes. This helper applies to any finite Galois extension
of number fields and any supplied local invariant family.

The elementary sign helpers turn products of nonzero real numbers into sums
of their sign classes in the rational numbers modulo the integers. The
quadratic CM Galois group is identified with the multiplicative form of the
additive group modulo two. The definition `quadraticCoordinate` uses complex
conjugation as its generator, so `quadraticCoordinate_complexConj` sends it
to the additive class of one.

For a CM number field `K` with maximal real subfield `F`,
`norm_pos_of_finiteLocalNorm K a ha` proves
`0 < Algebra.norm ℚ (a : F)` for every `a : Fˣ` satisfying that finite local
norm condition.

The proof chooses the invariant families supplied by the proved simultaneous
local class-formation theorem. The proved global reciprocity law is applied
to the quadratic carry class of `a`; its idele-class cohomology premise is
discharged by `ideleClassH1Vanishing`. Every finite invariant is zero by the
local helper. The archimedean invariant at a place above `v` is the sign class
of `v(a)`, since complex conjugation is the nontrivial quadratic automorphism.
Thus the sum of all those sign classes is zero. The product formula for the
rational field norm and `signClass_prod` identify this sum with the sign
class of `Algebra.norm ℚ a`. The class of one half is nonzero, so the rational
norm is nonnegative. It is nonzero because `a` is a unit, hence it is positive.

The positivity statement is a derived generalization of the source's check
for global integral units: the implemented reciprocity argument works for
every nonzero real element with the stated finite local norm witnesses.
The coordinate and sign lemmas are internal supporting constructions.
This module does not yet construct the half-weight Hecke character.
