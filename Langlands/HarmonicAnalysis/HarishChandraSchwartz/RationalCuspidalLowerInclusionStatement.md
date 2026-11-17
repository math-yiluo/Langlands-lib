# The lower inclusion of Theorem VIII.4.2 at an independent carrier universe

Waldspurger (2003), Theorem VIII.4.2, printed p.330 (PDF p.96), states
`p_χ(°C(G)) = A₂(G)_χ`, where `A₂(G)_χ` is the algebraic sum of the
coefficient spaces `A(ω)` of all discrete series `ω` whose central
character restricted to `A_G` is `χ`. The first paragraph of its proof,
on the same page, proves the inclusion
`A₂(G)_χ ⊂ p_χ(°C(G))`. It uses the wave packets `f_ψ` of VII.2,
Theorem VII.2.5 (`°f_ψ = f_ψ`, so `f_ψ` is cuspidal) and Fourier
inversion on `A_G` to isolate one coefficient of `ω` from the finite
fiber of its unramified orbit with central character `χ`. This module
states that inclusion as a closed proposition. It does not prove it.

## The proposition

`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.{u,uV}`
has exactly the structural binders of the published equality target
`RationalCuspidalDiscreteCoefficientStatement` in
`RationalCuspidalCentralStatements`: an arbitrary nonarchimedean local
field `F : Type u`, an affine locally finite type connected reductive
group scheme `G`, a maximal split torus, a generic cocharacter, a
compact open `K` with the minimal Iwasawa pair, a closed matrix
representation `ρ` on a nonempty finite index set, a split component
`s` with an arbitrary Haar measure `muA` on its literal point image,
an arbitrary Haar measure `mu` on the Borel quotient by that image, and
a continuous unitary character `χ`. Its conclusion is the set inclusion

`discreteSeriesCentralCoefficientSpace.{u,uV} A_G hA mu χ ⊆
rationalCuspidalCentralImage hKc hPK ρ muA χ`.

The left side is the carrier of the published canonical algebraic sum
of the actual coefficient spaces of all discrete-series classes, with
carriers in universe `uV`, on which `A_G` acts by `χ`. The right side is
the raw set of central integrals `p_χ φ` of actual cuspidal Schwartz
functions `φ`, defined without any convergence premise. Since the left
side is a sum of subspaces, the proposition also asserts that each
finite sum of coefficients is a single raw central integral.

There is no convergence, finiteness, admissibility, reproducing-vector
or decomposition premise. The carrier universe `uV` is independent of
the field universe `u`, so the proposition can be used both at `uV`
(for the level-lifting target, whose classes have carriers in `uV`) and
at `max u uV` (for the equality target). It is a derived realization
of the source inclusion on the Library's actual interfaces; the
universe-polymorphic phrasing is the only addition.

## Proved consequences

`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.supset`
restates the instance at carrier universe `max u uV`. Its type is,
choice for choice, the inclusion of the right side of the published
equality target into its left side. The proof is the hypothesis itself.

`RationalCuspidalDiscreteCoefficientLowerInclusionStatement.coefficient_mem`
assumes the proposition at `uV` and fixed structural choices. For every
subgroup `H`, every class `ω` in the published
`discreteSeriesCentralFixed A_G hA mu χ H`, and every `f` in the
coefficient space of its canonical representative `ω.val.out`, it
concludes `f ∈ rationalCuspidalCentralImage hKc hPK ρ muA χ`. The proof
places `f` in the algebraic sum by the published
`coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace`,
using the first component of membership in `discreteSeriesCentralFixed`
(that `A_G` acts by `χ`), and applies the proposition. This full-image
membership does not give the same-level membership required by
`RationalCuspidalFixedCoefficientLiftingStatement`; that needs the
separate compact averaging argument.
