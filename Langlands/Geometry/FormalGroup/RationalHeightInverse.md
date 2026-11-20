# Opposite signed kernel-rank heights for actual inverse maps

Harris, *Supercuspidal representations in the cohomology of Drinfel'd
upper half spaces* (1997), Appendix, printed p. 112 (PDF p. 38), gives the
height of a quasi-isogeny by the difference of the base-\(p\) logarithms
of the numerator and scalar kernel ranks after clearing a power of the
rational prime \(p\) locally. This derived construction keeps the rank
base \(q\) explicit and uses powers of an element \(\pi\) with nonzero
image in the coefficient field. In the formal local-field application,
\(\pi\) is a uniformizer and \(q\) is the residue cardinality.

On an open with a given height presentation, `toOpenTensor` takes its
integral isogeny and divides its tensor by the given uniformizer power.
The tensor over the open's section ring retains the numerator kernel
rank and gives the original rational section by scalar cancellation.
For coefficients localized from a domain to its fraction field, the
inverse calculation uses `HasPiHeight` at the same positive height on
the source and target. These hypotheses supply scalar divisibility and
all scalar-power ranks. The integral dual supplies a ranked presentation
of the inverse tensor. Its image in the sheaf is the actual inverse by
compatibility with composition and uniqueness of inverses. The scalar
kernel rank identifies the denominator height over a nontrivial ring of
sections when the rank base is at least two. The inverse signed rank
difference is therefore the negative of the original one. Applying this
construction on a presenting neighbourhood of each point gives pointwise
negation of the height function.

Evaluating a rational atlas quasi-isogeny on a test gives both its
forward and inverse coordinate tensors. Consequently the same negation
holds on every test of the original cover when the source and target
charts have the same positive scalar height.
