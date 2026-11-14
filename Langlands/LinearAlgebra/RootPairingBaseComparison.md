# Cartan comparison of bases of finite rational root systems

This internal construction compares any two supplied bases of the same finite
crystallographic rational root system. Its `baseEquiv` is an equivalence of the
two simple-root supports preserving all integer Cartan entries.

The height covector of a base takes the value one on each simple root. The
base's integer expansion of every root shows that evaluation on this covector
is its height. Since root heights are nonzero, the covector is regular and its
positive root set is the positive set of the base.

The imported finite Weyl orbit maximization argument aligns the signs of the
two height covectors. A root is simple exactly when it is positive and cannot
be expressed as a sum of two positive roots: height proves the forward
implication, and induction by addition of simple roots proves the reverse
implication. The Weyl automorphism therefore identifies the two simple
supports. Restricting its root-index equivalence constructs `baseEquiv`.
Preservation of root-coroot pairings and injectivity of the integer scalar map
prove equality of the corresponding Cartan entries.

For two possibly different rational root systems, a linear equivalence of their
root spaces and an index equivalence transporting every root already determine
a root-pairing equivalence, by the imported finite characteristic-zero
uniqueness result. Map the first base through this equivalence and compare it
with the second base by `baseEquiv`. The resulting `rootTransportBaseEquiv`
preserves every integer Cartan entry without assuming that the original linear
equivalence sends the first simple base to the second.

All bases are supplied and the root spaces are assumed to be spanned by roots
and coroots through `IsRootSystem`. No comparison with an actual algebraic
group or its integral root datum is asserted here. The proof is an internal
consequence of the imported root-system and chamber results; it uses no new
literature input.
