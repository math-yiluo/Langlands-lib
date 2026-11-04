# Lattice coordinate independence of actual smooth orbit sections

Author: Worker 200.

This derived comparison concerns the smooth orbit-section construction
motivated by Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), VI.1, printed
pages 295–296 (PDF pages 61–62). That passage defines coherent
coefficient sections on all equivalent representatives, tests smoothness
after restriction to a fixed compact picture and pullback to the unitary
character torus, and gives the diagonal invariant tensor model. The
coordinate comparison here is an internal prerequisite, rather than a
separately stated theorem in the source.

## Actual data and retained hypotheses

The setting is the existing canonical `SmoothRep` framework over `ℂ`.
`G : Type uG` is a locally compact topological group with
`NonarchimedeanGroup G`. `P`, `M` and `U` are actual subgroups,
`h : IsSemidirectDecomposition P M U`, and `U` and `P` are closed.
`K` is an actual compact open subgroup of `G`, and the displayed
factorization hypothesis is `G = P K`. The Levi projection
`h.projection` is continuous. The positive real unit-valued characters
`ν : I → (M →* ℝ≥0ˣ)` are continuous.

The fixed inducing object `π` is an actual canonical irreducible
admissible complex representation of `M`. The input
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)` gives a finite
torus parameter cover. The group, character-index, inducing-carrier,
two coordinate-index and lattice universes remain independent.
The result imposes no irreducibility premise on parabolic induction.

`L` is an additive commutative group with a displayed integer module
structure and finite bases `b : Basis J ℤ L` and
`c : Basis J' ℤ L`. These specify the intended integral coordinate
change. No claim is made that an arbitrary abstract multiplicative
equivalence of tori preserves the smoothness test.

## Coordinate reconstruction and the actual pullback

Let `T_bc = finiteTorusBasisChange b c`. It reconstructs a lattice
character from its values on `b` and evaluates it on `c`. The imported
scalar theory supplies its explicit integer monomial formula and smooth
real linear lift. `FiniteSmoothFamilyTransport` packages it as a
multiplicative equivalence and extends the scalar comparison to the
actual finite scalar-smooth coefficient sums.

`rebaseUnitaryTorusCoordinates ν e b c` is the actual equivalence

\[
 e'=T_{bc}\circ e.
\]

Its inverse sends `z'` to `e⁻¹(T_cb(z'))`. Consequently the literal
inducing representation at the new parameter `z'` is exactly the
representation at the old parameter `T_cb(z')`.

For any actual section `q : ProductInducedOrbitSections ν π h hU`,
`productInducedOrbitCompactPullback_rebase` proves

\[
 R_{e'}(q)=R_e(q)\circ T_{cb},
\]

where `R_e` means the existing actual orbit pullback followed by
`productInducedFamilyRestriction`. This is a definitional equality:
the parameter character, actual inducing representative, value of `q`
and normalized compact restriction agree. Thus the comparison retains
the actual fibers, vector transport and inverse-functional transport
of `ProductInducedOrbitSections`; it does not replace them with an
unrelated abstract function space.

## Equality of smooth section spaces

`productInducedSmoothOrbitSections_rebase` proves equality of
submodules of the same actual dependent section space:

\[
 C^\infty_{e'}(O,P)=C^\infty_e(O,P).
\]

Here the notation abbreviates the precise Lean submodules
`productInducedSmoothOrbitSections` with their displayed parameters.
Each imposes coherence under every actual inducing equivalence, and
finite scalar-smooth compact restriction in its own supplied coordinates.
The coherence condition is identical. The compact pullback identity
and `mem_finiteSmoothFamilies_comp_basisChange_iff c b` identify
the two finite-sum conditions, proving equality.

`productInducedSmoothOrbitRebaseEquiv` is the resulting linear
equivalence. Its forward and inverse application theorems say that
both maps have value `q(A)` at every actual orbit representative `A`.
It changes no actual orbit-section value. All assertions use the
finite scalar-smooth convention of `SmoothTensorFamilies`; comparison
with a manifold-valued smoothness definition remains separate.

This result handles explicit integer lattice coordinate changes of the
supplied cover. Comparisons after changing the fixed base representation,
the discrete-series full-stabilizer comparison, actual rational reductive
realization, comparison of the imported normalization with the source's
Levi-inflated normalization, normalized intertwiners, wave packets and
the analytic Plancherel assertions remain separate obligations.
