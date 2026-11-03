# Root-sign length determines the simple generators

This internal module works with a finite crystallographic root pairing over a
linearly ordered field, a linear functional nonzero on every root, and an
arbitrary Coxeter system on its Weyl group indexed by that functional base.
`RootSignLengthLaw` is the right-multiplication length criterion using those
literal root labels. The theorem proves that each supplied simple generator
is the reflection in its labelled root. No reducedness or spanning assumption
is added.

For a supplied generator s at a simple root α, the length law first shows
sα is negative. Let t be the actual reflection in α. Since tα is negative,
the supplied length decreases on right multiplication of t by s, so ts sends α
to a positive root. Distinct supplied generators have product length two,
so s sends every other simple root β to a positive root. If tsβ were negative,
the simple-reflection sign-change criterion from `RootPairingSigns` would
make sβ a natural multiple of α. Applying s again would make β a natural
multiple of the negative root sα, contradicting positivity. Thus ts sends all
simple roots positive. The published canonical root-pairing Coxeter system
has a right descent at every nonidentity element; its length criterion now
forces ts to be identity. The supplied involution then gives s = t.

The argument derives its conclusion from the published canonical Coxeter
existence theorem and the finite-root coefficient sign-change lemma. It does
not assume that the supplied generators already act as root reflections.
Actual scheme and rational-point transport and the Aubert compatibility
equation are separate applications.
