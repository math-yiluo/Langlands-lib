# Inversion decrease for union/intersection replacement

This module proves the numerical segment comparison used in Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), §6.7,
printed p.190/PDF27. The registered original is `zelevinsky-1980-induced-ii`,
SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The original's final lemma controls precedence contributions of an outside
segment when a linked pair is replaced by its union and intersection.

`IsUnionIntersectionReplacement Δ Γ U I` records equality of the actual
support of `U` with the union. For `I = some J`, it records that `J` has the
intersection support. For `I = none`, it records an empty intersection. The
replacement list is `U :: I.toList`; an empty intersection contributes no
segment, as segments have positive length.

Assume `Δ` precedes `Γ`, and explicitly supply integral-twist freeness.
The implementation places their intervals at `[a,b]` and `[c,d]`, with
`a < c ≤ b+1` and `b < d`. Support extensionality identifies the union
with `[a,d]` and a nonempty intersection with `[c,b]`.
An outside segment related to either new segment lies on the same integral
twist line. The endpoint precedence criterion and integer arithmetic show
that its total incoming or outgoing contribution to the two new segments
does not exceed its contribution to the original two. If it is related to
neither, the new contribution is zero. The empty-intersection case is
handled directly with just the union.

There is no internal inversion in the replacement list: the intersection
is contained in the union. The original ordered pair has exactly one
internal inversion. The generic occurrence-sensitive replacement theorem
therefore gives a strict decrease for the full lists with arbitrary fixed
prefix and suffix. All outside occurrences and multiplicities are retained.
The argument does not require the collection of embedding data to be finite.

The support predicate, explicit-freeness endpoint derivation, and full-list
inequality are internal formal elaborations of the cited elementary lemma.
No representation-theoretic reduction, product commutation, irreducible
socle existence, or exhaustion result is used or proved here.
