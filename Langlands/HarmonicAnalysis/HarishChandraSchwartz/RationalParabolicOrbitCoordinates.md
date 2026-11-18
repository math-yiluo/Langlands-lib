# Actual norms of maximal-parabolic orbit coordinates

This unit proves the actual-point coordinate estimates used in step (2)
of Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, Lemma II.3.5, printed pp.257–258.
The original is registered as `waldspurger-2003-plancherel`,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The selected predicate `HasOrbitCoordinateNeighborhoodRecovery` says
that every open subgroup of the supplied opposite radical contains
all points whose off-line orbit coordinates are sufficiently small:
for some `C5 > 0`, each coordinate other than `j` has norm at most
`exp(-C5)`. Norms throughout are the actual residue-normalized
absolute value of the local field.

The coordinate and scalar identities begin over any field.
`HasExactCoordinateLineStabilizer.isRationalLineStabilizer` transports
the exact subgroup-functor condition to actual rational points,
using the isomorphism from sections on `Spec F` to `F`.
`HasTorusCharacterDiagonal.rationalMatrix_conj_entry` computes the
`(r,j)` coefficient of `tau(a*g*a⁻¹)` as the original coefficient
times `chi_r(a)/chi_j(a)`. The diagonal-character equation holds
in the one fixed torus basis already supplied by the algebraic
construction. `rationalMatrix_line_entry_eq_one_of_mem_opposite_unipotent`
specializes the identity block of the opposite dynamic unipotent:
its distinguished `(j,j)` entry is exactly one.

For a local field, `norm_character_ratio_eq_exp` identifies the norm
of the character ratio with

```text
exp(log(q) * order(chi_j - chi_r)(a)).
```

Here `q` is the actual residue cardinality. The sign follows from
`|chi(a)| = q^(-order(chi)(a))`.
`maximalParabolic_orbitOrder_gap` transports the algebraic omitted-root
gap to every actual point `a` with nonnegative simple-root orders.
The intrinsic uniformizer-section theorem supplies a cocharacter
whose pairings equal every actual character order. Consequently the
compact torus factor causes no error in these character comparisons.
For `alpha` simple and `zeta` standard for `Delta \ {alpha}`, put
`m = <alpha,zeta> > 0`. The proved actual inequality is

```text
order(alpha)(a) <= m * order(chi_j - chi_r)(a)
```

whenever the off-line orbit coordinate is nonzero. It assumes the
actual maximal split torus, connected reductive group, generic
cocharacter, fixed torus diagonalization, and preservation of the
chosen line by both the minimal and selected maximal standard
parabolics. These choices are available from the preceding
`exists_maximalParabolic_orbitPairing_gap` construction and its
exact stabilizer. They are not analytic estimates supplied as
hypotheses. `maximalParabolic_orbit_norm_growth` therefore gives
exponential coordinate growth under conjugation with constant
`log(q)/m`. Zero coordinates satisfy the same inequality directly.

`exists_orbitCoordinate_exp_bound` proves a common upper bound
`|tau(g)_(r,j)| <= exp(C*(1 + rationalHeight rho g))`, with `C > 0`,
for every entry and every point. Its source representation `rho`
is any supplied nonempty finite closed matrix realization. The
published polynomial matrix-norm comparison controls `tau` in this
original height; no adapted matrix realization is assumed.
`exists_orbitCoordinate_lower_bound` proves that, on any compact
set, some coordinate in column `j` has norm at least `exp(-D)`
for a common `D >= 0`. A uniform bound for the inverse matrices,
followed by the sup-norm matrix action bound, controls the column
away from zero. Finally,
`IsRationalLineStabilizer.orbitCoordinate_mul` proves that right
multiplication by a parabolic point scales every coordinate in the
column by the norm of a single nonzero field unit.

The small-coordinate implication is proved by compactness rather
than by constructing an inverse to an algebraic orbit map.
`exists_small_orbitCoordinates_mem_open` assumes a closed rational
subgroup `U`, distinguished coordinate one, a trivial stabilizer of
the vector `e_j` in `U`, and a bound for the norm of `rho(u)` by a
power of `max(1, norm(tau(u)e_j))`. The subset of `U` on which all
orbit coordinates have norm at most one is closed and lies in a
compact sublevel of the supplied closed `rho`. On its complement
of any given open subgroup, the continuous function
`norm(tau(u)e_j - e_j)` has a strictly positive minimum, since its
zero fiber is exactly the identity. Taking the smaller of one and
half this minimum proves the implication. The empty-complement
case is handled separately.

`hasOrbitCoordinateNeighborhoodRecovery_of_parabolic_line`
discharges those auxiliary assumptions for the actual opposite
dynamic radical. Closedness follows from its represented closed
subgroup. The distinguished coordinate follows from the diagonal
cocharacter identity. Exactness of the parabolic line stabilizer
and the trivial intersection of opposite unipotent and parabolic
give the trivial vector stabilizer. The published
`exists_rationalMatrixNorm_le_of_weightVector` supplies the
orbit-height bound. The resulting positive coordinate threshold
is decreased to `exp(-C5)` with `C5 = abs(log(epsilon)) + 1`.
This argument requires an affine ambient group and a supplied closed
finite matrix realization, but does not require separability of an
orbit map or characteristic zero.

All results retain arbitrary field universe and both local-field
characteristics. This unit supplies coordinate estimates toward
II.3.5. It does not assert the density-extension or two-parabolic
intersection conclusion of that lemma, the opposite-radical tail
cutoff, or the final VIII.3.1 integral estimate.
