# An actual boundary cocharacter for a supplied parabolic presentation

This internal construction starts from an actual compatible parabolic root
presentation and a vector in its nonnegative restricted-root cone outside its
strictly positive cone. It constructs an integral cocharacter of the original
Levi split component, and maps it to the original maximal split torus.

The finite family consists of the original complementary simple roots,
restricted to the original split component. Its coefficients are precisely
`nonnegRootCoefficients`, including their chosen expansion of the given vector.
Reindexing this expansion by the finite subtype preserves repetitions under
restriction. The finite-character boundary construction then gives a genuine
integral cocharacter nonnegative on these characters, positive on at least one
of them, and zero on every character with positive coefficient.

Selected simple roots already restrict to zero on the split component.
Consequently the mapped cocharacter is nonnegative on every original simple
root, and its zero simple-root face contains `boundaryRootIndex`. It is standard
for this actual zero face. For a connected reductive ambient group, the proved
root-sign inclusion criterion shows that its dynamic parabolic contains the
original parabolic on every test scheme. A positive simple-root pairing and
the negative of that root show that this dynamic parabolic is proper.

These results construct the cocharacter and prove functor containment and
properness. They do not yet choose actual models for the coarser parabolic,
its Levi and radical, or assert exponent projection or the complete VII.2.4
equivalence.
