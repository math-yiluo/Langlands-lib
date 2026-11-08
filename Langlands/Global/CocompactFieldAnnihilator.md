# The annihilator of a cocompact infinite field

`fieldAnnihilator` is the additive subgroup of ring parameters whose
multiplication characters are trivial on the image of the field. This internal
supporting module proves that it equals that field image when the field is
infinite, the ring has compact representatives modulo the field, the character
is continuous and field-trivial, and its multiplication pairing is nondegenerate.
The field and ring may have different universes.

The reverse inclusion follows directly from field triviality. For the forward
inclusion, fix an annihilating parameter a. For each field scalar s choose a
representative c(s)=iota(s)*a-iota(k(s)) in the compact set. Every c(s)
annihilates the field. Choose a neighborhood W of zero such that the difference
of any two elements of W lies in the small-parameter neighborhood from
`CocompactPairingSeparation`. Finitely many translates of W cover the compact
representative set. Since the field is infinite, two distinct scalars s and r
have representatives in the same translate.

Their difference is both small and field-annihilating, so the small-parameter
lemma says it annihilates the whole ring. Nondegeneracy makes that difference
zero. Rearranging c(s)=c(r) gives
iota(s-r)*a=iota(k(s)-k(r)). Dividing by the nonzero field scalar s-r writes
a as a field image. No topology on the field or closedness assumption on its
image is needed for this finite-cover argument.

This is an internal implementation of G5 in Worker 1843's proof plan. Using
all field scalars instead of natural-number multiples requires only an infinite
field; the intended actual number fields meet that condition. The module does
not assert full character surjectivity or topological self-duality.
