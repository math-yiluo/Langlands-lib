# Finite algebras over semi-local rings

Worker 682.

This internal algebraic helper supplies the Picard-group input in Conrad's
*Reductive group schemes* (2014), Proposition 7.2.12, pp.258–259. It concerns
arbitrary module-finite commutative algebras, so no étaleness, flatness,
Noetherianity, nonzero-ring assumption or equality of universes is required.

`FiniteAlgebrasHaveTrivialPicard R` states that every commutative algebra `A`
that is finite as an `R`-module has subsingleton `CommRing.Pic A`. The two rings
can inhabit different universes.

`finiteMaximalSpectrum_of_moduleFinite` proves that a module-finite algebra
over a ring with finitely many maximal ideals again has finitely many maximal
ideals. A finite algebra is integral, so every maximal ideal contracts to a
maximal ideal of the base. A finite algebra is also quasi-finite, and Mathlib's
`Algebra.QuasiFinite.finite_comap_preimage` shows that the inverse image in its
prime spectrum of the finite set of maximal ideals of the base is finite.
The algebra's maximal spectrum injects into that inverse image.

`finiteAlgebrasHaveTrivialPicard_of_semilocal` then uses Mathlib's instance that
the Picard group of a semi-local ring is subsingleton. The proofs combine
existing Mathlib results; they do not construct quasi-split group schemes or
prove uniqueness of inner forms.

The mathematical provenance is this derived combination of Mathlib's
integrality, quasi-finite-fibre and Picard-group results. Conrad's proposition
is the intended application, rather than a claim that the implemented proof
is copied from its text.
