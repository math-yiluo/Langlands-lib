# Determinant characters and scalar determinant representations

Worker 17 authored this construction. `determinantCharacter A`
is the actual homomorphism to coefficient-field units obtained by applying
Mathlib's basis-independent linear determinant to the invertible action
operators. `determinantCharacter_apply` identifies its scalar value with
`LinearMap.det (A.representation g)`.

For an actual representation equivalence, the intertwining equation gives
conjugate action operators. `determinantCharacter_eq` applies Mathlib's
determinant invariance under that linear conjugation, allowing independent
carrier universes. This certifies `determinantCharacterClass` on the genuine
isomorphism quotient.

`determinant A` realizes this character on the actual scalar vector space
`K`, using the published `Langlands.characterRepresentation`. Its rank is
proved to be one. `determinantEquiv` uses the equality of determinant
characters and the identity linear equivalence, and certifies
`determinantClass`. Rank-zero inputs are allowed. This scalar realization
does not choose a basis or claim to be a chosen identification of an
exterior-power line. Nor is a determinant functor on arbitrary morphisms
between unequal-dimensional spaces asserted.

Source correspondence: Henniart 2000, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique*, §1.2(1), printed page 440,
uses the determinant of the Weil representation as a one-dimensional
character. Literature ID `henniart-2000-simple-proof`, PDF SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The construction and quotient obligations are intrinsic algebraic
implementation work.

Dependencies: the published `Langlands.Weil.Representation.Basic` foundation
and Worker 4's `Langlands.Representation.Twist.Definitions`, both in Library
commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`. The twist Lean SHA-256 is
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
Pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`
provides `Representation.asGroupHom`, `LinearMap.det` and
`LinearMap.det_conj`. Existing project code is imported, not copied.
