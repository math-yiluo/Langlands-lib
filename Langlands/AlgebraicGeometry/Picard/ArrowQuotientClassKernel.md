# The full kernel of the actual etale Picard family map

This internal construction starts with the full represented actual-arrow
presheaf and its full endpoint-kernel presentation, as in
`ArrowQuotientEndpoints`. It identifies the canonical sheaf of arrow classes
with the kernel of the actual etale family-class map on every test scheme.

The descended endpoints have equal etale Picard class because they do so on
actual arrows; the universal property of the canonical quotient extends this
equality to all sections. Their joint injectivity follows from the previously
proved endpoint monomorphism.

If two family points have equal etale class, the local injectivity of
sheafification gives a covering sieve where their unsheafified groupoid classes
are equal. Such equality is witnessed by actual bundle isomorphisms. These
arrows give local sections of the canonical arrow-class sheaf. Joint endpoint
injectivity makes the local sections compatible. Sheaf gluing produces a
section over the entire test scheme, and separatedness of the represented
endpoint sheaf recovers the two prescribed endpoints.

`arrowKernelQuotient_relation_iff` gives both directions of this
characterization on the full section types. Together with joint endpoint
injectivity, it proves `arrowKernelQuotient_isPullback`, the kernel-pair square
of the actual etale family map as a square of presheaves.
`arrowKernelQuotient_sectionwise` derives reflexivity, symmetry and transitivity
from equality of the etale family classes. This route obtains the relation laws
without choosing global actual-arrow representatives for arbitrary sheaf
sections.

`arrowKernelQuotientKernelIso` is the resulting natural isomorphism from the
canonical arrow-class sheaf to the categorical pullback of the etale family
map with itself. Its two projection equations preserve the actual ordered
endpoints.

This is a derived categorical consequence of the published actual groupoid,
class map, and arrow-kernel quotient constructions. It uses no geometric
quotient theorem and asserts no algebraic-space representability or smoothness
for the quotient.
