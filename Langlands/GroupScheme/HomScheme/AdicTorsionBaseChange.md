# Scalar extension of algebraized torsion restrictions

Let `A` be a complete Noetherian local ring with maximal ideal `m`, and let the
formal split-torus homomorphism be given on the quotients `A / m^(d + 1)`.
For `n > 0`, `Adic.System.splitTorsionHom` algebraizes its restriction to the
full scheme-theoretic `n`-torsion, the kernel of multiplication by `n`.
Its character group is `(L → ℤ) / n(L → ℤ)`, and it is finite locally free
of rank `n ^ |L|`. The finite-source adic theorem gives the algebraization,
and `splitTorsionHom_reduce` identifies its reduction at every level with the
original formal map composed with the base-changed inclusion.

`Adic.System.pull_precompose` checks at each quotient that pulling a formal
system along a ring map commutes with precomposition by a source homomorphism.
It uses composition of relative Hom pullbacks and the comparison between
iterated and composite base change. Consequently `baseChange_finiteRestriction`
compares the algebraized finite restriction with the corresponding restriction
of an actual lift over the new ring, whenever quotient reduction there detects
equality of the two maps from the finite source.

`Adic.System.baseChange_splitTorsionHom` applies this comparison to positive
torsion for a ring map `φ : A → B` and a homomorphism over `B` whose reductions
form `s.pull φ`. The ring `B` must be separated for the extended ideal
`(maximalIdeal A).map φ`. A separated target stays separated after base change,
and the finite source stays diagonalizable, so
`diagonalizableAdicInjectivity_of_iso` gives the equality from the reductions.

This is an internal comparison for the proof of adic Hom effectivity. It uses
the finite-source algebraization (`FiniteSourceAdicHom`) and the algebraized torsion
restrictions (`AdicTorsionRestriction`).
