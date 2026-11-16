# Finite coefficient homomorphisms over arbitrary algebras

Worker 700. Proof of the internal arbitrary-algebra homomorphism descent
statement used in the arbitrary-base approximation step of Conrad,
*Reductive group schemes* (2014), Theorem 5.3.5, p.166.

The construction uses the published finite-coefficient descent of morphisms and
equalities of morphisms. A map which becomes a group homomorphism after base
change to an arbitrary algebra satisfies its unit and multiplication equations
over a finitely generated coefficient subalgebra. The two equations descend
separately and hold over their common finitely generated join. Equality over a
coefficient subalgebra persists over all larger subalgebras by projection through
the corresponding pullbacks. No fraction-field or flatness assumption is used.

For the full supplied-homomorphism construction, the underlying scheme map
first descends to a finite coefficient subalgebra `T`. The canonical
direct/iterated pullback isomorphisms identify its base change with the
given homomorphism. The eventual homomorphism result gives a finitely generated
`T`-subalgebra `U` of `A` where the two equations hold. Restricting scalars
makes `U` a finitely generated `R`-subalgebra. Conjugation by the canonical
group scheme pullback comparisons then produces the required group
homomorphism over `U`. Its recovery equation is checked by the two projections
of the target pullback, using the scheme-map descent equation.

The target is
`Langlands.GroupScheme.Descent.FiniteCoefficient.HomGeneralStatement`.
The theorem `homGeneral` proves this exact published proposition, uniformly
in every universe. Its assumptions are precisely the quasi-compact and
quasi-separated source and locally finitely presented target in that
statement. This proof descends a supplied homomorphism between already
defined groups; group-object approximation, eventual monicity and reductivity,
and the closed-immersion theorem remain separate obligations.
