# Isogenies of reduced root data carry bases to bases

This proof module proves the published proposition
`Langlands.LinearAlgebra.RootDatumIsogenyBaseStatement` with its six independent
type universes and unchanged hypotheses. The entry theorem is
`Langlands.LinearAlgebra.rootDatumIsogenyBase`.

The source is Brian Conrad, *Reductive group schemes* (2014), Lemma 6.1.12,
p.194, registered as `conrad-2014-reductive-group-schemes`. The statement's
Markdown explains the direction of the isogeny and the correspondence of the
root indices with Conrad's notation. This implementation follows the source's
choice of a functional and pullback, using integral functionals throughout.

For the given base of the second datum, pairing with the sum of its positive
coroots gives a functional with value 2 on every simple root. Reflection in a
simple root permutes the other positive roots and negates their pairings with
that root, so their total contribution is zero. Induction by addition of simple
roots proves that the functional detects precisely the given positive roots;
applying this to a root or its negative proves nonvanishing on every root.

Pulling back along the weight map preserves the signs, because each root is
carried to a strictly positive integer multiple of the corresponding root. The
integral base construction from
`Langlands.GroupScheme.SplitExistence.IntegralBase` then supplies a base for the
first datum with these signs. Its root support is `baseOf` for the functional.
The copolarization supplies a coroot functional of the same signs, and the
imported equality of the root and coroot `baseOf` sets verifies both sets of
base axioms.

Finally, a positive root is simple if and only if its reflection preserves
every other positive root. For the reverse implication, a nonsimple positive
root is a sum of two positive roots; reflecting both summands would make a
negative root have positive functional value. The transpose-pairing and root
and coroot transport identities imply that the weight map commutes with
corresponding reflections. Applying the criterion to the two bases identifies
their supports.

The private helpers are internal derivations for this proof. Their arguments
adapt the positive-coroot sum in `SplitExistence.ShortRoots`, the integral
constructor in `RootDatumCoweightFace`, the indecomposable-root argument in
`Reductive.RootDatumGaloisSimpleRoots`, and the reflection comparison in
`RootDatumIsogenyChambers`. Those modules impose shared universes on some
lattice types; the helpers here retain independent universes. The imported
integral construction and Mathlib base lemmas already allow independent
universes. No target or imported source is modified.
