# Finite exponent norms for the full unitary induced Jacquet family

This derived module proves a uniform spectral property of the actual family
`r_Q i_P(σ ψ)` for an admissible finite-length representation `σ` of the actual
source Levi and every unitary unramified source twist `ψ`. All represented
parabolic, rational Levi, geometric radical, and multiplication-isomorphism data
remain the specified ones. The field and representation carrier universes are
independent.

`unitaryInducedJacquetExponentNormSet` collects the nonnegative real norms at one
specified point of the target component of every generalized eigencharacter of
the full actual normalized Jacquet-induction composite throughout all unitary
unramified twists. The point acts through its original map to the target Levi.

The published represented geometric lemma constructs finitely many actual
intersection data and a filtration of that entire functor. Each target split
component factors through a split component of the corresponding inner Levi.
The fixed finite norm theorem for each full piece then applies. Every
character of the filtered representation occurs in one of its graded pieces by
the published generalized-eigencharacter filtration theorem. Consequently the
family norm set is a subset of a finite union of finite sets and is finite.

Taking the supremum of its elements strictly below one gives a common `θ < 1`
for all exponent norms that are strictly contracting at the specified point.
The empty set has supremum zero, so this includes the case of no such exponents.

This is supporting infrastructure for the uniform root bounds in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*
(2003), source `waldspurger-2003-plancherel`, proof of VI.2.1 on printed
pp.297–298 and of VI.2.3 on printed p.300. The implemented route composes the
actual geometric lemma, actual piece exponent untwisting, Jacquet exponent
finiteness, and filtration transfer. It imposes no generic-locus restriction.
It does not prove that every nonunitary exponent is strictly contracting, a
uniform nilpotence order, comparison with the literal standard-subgroup
induction model, or the principal positive-decay target.
