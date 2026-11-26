# Adding compact-level invisibility to separation by proper induction

Fix an equivalence-invariant condition on irreducible representations. Suppose
it contains the unramified orbit in question and all irreducibles satisfying it
have nonzero `J`-fixed vectors. Suppose each properly induced twisted distribution
belongs to either the span of irreducible distributions satisfying the condition
or the span of those failing it.

`TwistedPseudoCoefficientSupportProjectionStatement` uses the entrywise
automorphism on `GL_n(E)` for a field `E` with its `F`-module topology. It takes
the Borel, Hausdorff, locally compact and totally disconnected group structure
and a Haar measure. It assumes every open subgroup contains a compact open
subgroup preserved by the inverse automorphism. The induction hypothesis ranges
over the actual unnormalized induced distributions of admissible irreducible
Levi pairs of the prescribed carrier universe and assumes the induced action is
admissible.

Twisted character independence gives a linear projection onto the first span that
kills the second. It fixes the orbit span and kills the `J`-invisible span. It
preserves the other essentially tempered span because each of its generators is
an irreducible twisted distribution, on which the projection acts by identity or
zero. The proper induction hypothesis gives the same property on each properly
induced generator. An element of the orbit in the full complementary span is
therefore, after applying the projection, already in the complementary span with
only the other essentially tempered characters and proper inductions. Separation
from that smaller sum gives zero.

This is a linear-algebra consequence of twisted character independence in
Henniart–Lemaire II.2.8, applied to the separation used in II.5.13.
`exists_compact_open_fixed_constituentTwists` supplies a visibility bound when
the selected classes are twists of constituents of finitely many finite-length
smooth representations.
