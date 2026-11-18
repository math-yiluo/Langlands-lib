# Finite indecomposable actual absolute Cartan matrices

This proves the internal intermediate statement
`AbsolutelyAlmostSimpleFiniteCartanStatement` using the supplied integral
absolute root datum, rationalized without changing its simple support.

The proof first transports finite Cartan and indecomposability properties
along an equivalence preserving all ordered entries. It then applies the
published `IsRootDatumOf.rationalBase` and
`cartanMatrix_rationalBaseSupportEquiv` interfaces to a split maximal torus.
The full actual rational root pairing is irreducible by
`isIrreducible_fullRelativeRootPairing`. The integral datum supplies
reducedness, and Mathlib gives finite Cartan and indecomposability for the
rational base's Cartan matrix. Nonemptiness follows from the existence of an
actual root in a split maximal torus of an almost-simple group.

For an actual Tits index, apply this argument to its pinning over the separable
closure. Absolute almost-simplicity persists over that algebraic extension by
the published `IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension`.
The resulting integer Cartan entries are those of the original pinning base.
No local classification or local Kneser--Tits theorem is used.
