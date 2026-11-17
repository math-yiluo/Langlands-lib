# Waldspurger's Lemma II.3.1 on actual rational points

Author: Worker 248, Task 5460, revision 1.

The proposition `Langlands.HarishChandraSchwartz.RationalSigmaProductStatement`
asserts the second inequality of Waldspurger's Lemma II.3.1 for every actual
standard parabolic over a nonarchimedean local field, at arbitrary universe `u`.
The theorem `rationalSigmaProduct` proves it, and
`rationalSigmaProductBound` is its specialization to one group and parabolic.

Let `G` be connected reductive, `i : S → G` a maximal split torus, `ν` generic,
and `J` a subset of the simple relative roots. For any closed matrix
representation `ρ : G → GL_N`, with `N` nonzero, there is a positive real `C`
such that

`C (1 + max (σ(m), σ(u))) ≤ 1 + σ(m u)`

for every `m ∈ M_J(F)` and `u ∈ U_J(F)`, where `σ = rationalHeight ρ`.
There is no compact subgroup, basis or Cartan premise. This supplies the exact
`SigmaProductBound` input of `constantTermEstimate_of_bounds` for the
standard radical appearing in `RationalConstantTermEstimateStatement`.

## Source and provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
Lemma II.3.1, printed pp.254–255, and the proof of Proposition II.4.5,
printed pp.262–263. Source ID `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

The source states two comparisons for semistandard parabolics. This module
proves the second comparison for the actual standard parabolics. The
implementation uses the Library's published projection-height bound instead
of repeating the source's change of matrix coordinates.

## Implemented proof

The published `exists_rationalHeight_projection_le` provides a nonnegative
constant `c` such that the height of the Levi projection of `q ∈ P_J(F)` is
at most `c + σ(q)`. The published semidirect decomposition identifies the
projection of `m u` with `m`, giving `σ(m) ≤ c + σ(m u)`.

Height subadditivity and invariance under inversion then give
`σ(u) ≤ σ(m) + σ(m u) ≤ c + 2 σ(m u)`. Nonnegativity of height implies
`1 + max (σ(m), σ(u)) ≤ (c + 2)(1 + σ(m u))`. The abstract helper
`sigmaProductBound_of_le_add_mul` implements this calculation and takes
`C = (c + 2)⁻¹`.

This module establishes no weighted unipotent integrability, spherical
upper or lower estimate, or constant-term estimate.
