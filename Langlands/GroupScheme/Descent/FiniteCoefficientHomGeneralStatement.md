# Finite coefficient descent of homomorphisms over arbitrary algebras

`Langlands.GroupScheme.Descent.FiniteCoefficient.HomGeneralStatement`
is an internal finite coefficient descent statement, uniform in the universe.
Let `A` be an arbitrary commutative `R`-algebra. Let `G` and `H` be actual
group schemes over `Spec R`, with `G` quasi-compact and quasi-separated over
`R` and `H` locally of finite presentation over `R`.
Every supplied group homomorphism between their base changes to `A`
descends to a group homomorphism over a finitely generated `R`-subalgebra
of `A` containing any prescribed finite subset.

The displayed equation in Lean says that base change of the descended
homomorphism recovers the supplied homomorphism, using the canonical group
scheme isomorphisms between iterated and direct pullbacks. It is an equality
of actual group scheme homomorphisms.
There are no domain, fraction field, flatness or separatedness assumptions.

This statement is an internal prerequisite for the arbitrary-base limit step
in Conrad, *Reductive group schemes* (2014), Theorem 5.3.5, first paragraph
of the proof on p.166. Its more general formulation isolates a construction
from finite presentation: first descend the underlying scheme map, then
descend its unit and multiplication equations to larger finite coefficients.
It extends the fraction field construction in
`Langlands.GroupScheme.Descent.FiniteCoefficient.exists_fg_hom`.
It asserts neither a noetherian model for the groups themselves nor the
closed-immersion theorem.
