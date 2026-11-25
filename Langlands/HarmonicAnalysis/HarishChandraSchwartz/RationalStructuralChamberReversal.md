# Reversing the structural chamber

This derived module reverses the chamber used by the
structural inputs of `RationalConstantTermEstimateStatement`. Its motivation
is the change of minimal parabolic in Waldspurger's remark following
Proposition II.4.5, printed p.263.
The module
`Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalStructuralChamberReversal`
defines `RationalStructuralChamberReversalStatement.{u}` and proves it by
`rationalStructuralChamberReversal`, at arbitrary field universe `u`.

Replacing the generic cocharacter `ν` by `-ν` and the simple-root subset `J`
by its negative preserves the actual standard Levi. It exchanges the
standard and opposite radicals. The same compact subgroup `K0` retains
`SimultaneousStandardBasisAt`, and the ambient and Levi Cartan covering
properties are preserved.
The preservation implications hold for any supplied subgroup `K0`; when
`K0` is compact open, its topology is unchanged.

For the basis theorem, the original compact-open normal family is retained.
For each reversed face, choose the original negated face and its existing
compatible split component. The published reversal theorem for compatible
components gives the same component for the reversed Levi. Inversion
reverses the order of the three actual intersection factors in an Iwahori
decomposition. Inverting a chamber point negates all its character
inequalities and exchanges the two weak contraction clauses. The published
weak-Iwahori reduction reconstructs normalization and every strict and
uniform contraction clause from these weak clauses. Thus the proof preserves
the full simultaneous-basis property, including the inherited normal
compact-open family in every Levi.

For either Cartan covering, decompose the inverse of the given point.
Invert the expression, the two compact factors and the finite centralizer
factor. A centralizer point commutes with the torus point, so the expression
has the required order. Inverting the torus point negates its chamber
inequalities. The new finite family consists of the inverses of the old one.

These are structural transport results. They do not compare the spherical
functions for the two minimal parabolics, establish a modulus reciprocity
formula, or prove any weighted unipotent estimate. Those comparisons are
separate steps of the actual constant-term proof; the comparison of the
spherical functions is `rationalXiChangeMinimal` (module `RationalXiChangeMinimal`),
the modulus reciprocity is `rationalReversedModulus` (module
`RationalReversedModulus`), and the weighted unipotent estimate
`RationalUnipotentWeightIntegrabilityStatement` remains unproved.

Source motivation: J.-L. Waldspurger, *La formule de Plancherel pour les
groupes p-adiques, d'après Harish-Chandra* (2003), literature ID
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
Proposition II.4.5 and the following change-of-parabolic remark, printed
pp.262–263. The exact Library structural predicates and their reversal are
derived content, not separately numbered assertions in that source.
