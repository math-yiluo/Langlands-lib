# Independence of roots transformed by ordered reflection prefixes

This internal linear-algebra argument supports the actual split Steinberg product
comparison. It uses only the displayed reflection laws and Mathlib's root-pairing
base, and does not assert a geometric immersion.

`orderedReflectionWeights r a f` sends `j` to
`orderedPrefix r f j.castSucc (a j)`. For independent vectors `a j` over a
commutative ring and linear automorphisms
`f j` with `f j z = z - l j z • a j` and `f j (a j) = -a j`, the vectors
`orderedPrefix r f j.castSucc (a j)` are independent and have the same span as
the original family. Prefixes use the given order; the factor at position `j`
is acted on by precisely the preceding automorphisms.

The proof inducts on the length, proving independence and span equality together.
The transformed family consists of `a 0` followed by the image under `f 0` of
the transformed tail. Subtracting multiples of `a 0` preserves the span after
adjoining `a 0`. Tail span equality and original independence show that adjoining
`-a 0` to the transformed tail is independent, using the ring-general coefficient
criterion. Applying `f 0` gives the desired family, since it sends `-a 0` to
`a 0`. The empty family is included.

`prefixSimpleRoots_linearIndependent` applies this result to any ordered base of
a root pairing. Its hypotheses are the base's independence and the defining
reflection and self-reflection identities. In particular the result is integral
when the coefficient ring is the integers; it does not reduce the roots to the
characteristic of a field.
