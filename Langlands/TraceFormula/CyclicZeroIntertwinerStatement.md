# Global intertwining at zero for the discrete trace summands

Arthur and Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), II §9, (9.2), printed p. 132, and III (4.1)–(4.2),
printed p. 203, use the value of the global standard intertwining operator
`M(s, λ)` at `λ = 0` on the discrete induction. The scalar comparison with
the normalized operators is a further input in III (4.3)–(4.4), pp. 208–209.

`WeylIntertwiningData` retains the root chamber of the actual parabolic,
the split component of the Levi, and the conjugation by the inverse of
an actual ambient rational representative. `HasExpansion` requires a
finite expansion and absolute convergence of the global intertwining integral
on a nonempty regular chamber. Its coefficients are meromorphic in coordinates
with domain of holomorphy containing the imaginary axis. `IsImaginaryFamily`
is the Library's evaluation of such continuations in the compact picture.
These predicates specialize the Library's square-integrable expansion and
imaginary intertwining interfaces.

`IsRestrictedZeroValue` compares the operator with the ambient family at
zero inside the common Hilbert space. The two supported slices can differ.
`IsRegularZeroIntertwiner` specializes it to the specified coordinate
permutation and the full discrete slice. It requires a chamber expansion
for each generating section, so the evaluation condition applies on the
generators. The identity Weyl element has the identity operator. The
existence proposition `CyclicZeroIntertwinerStatement` concerns exactly
these operators with the standard compact picture and nonnegative slice
parameter.
