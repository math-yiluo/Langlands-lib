# Strict orbit weights of an actual parabolic eigenline

This unit supplies the algebraic coordinate gap used in Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Lemma II.3.5, proof step (2), printed pp.257–258:
the third listed condition requires a positive constant controlling
every nontrivial coordinate character by the omitted simple-root
coordinate. The original is registered as
`waldspurger-2003-plancherel`,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).

`HasStrictOrbitWeightUpperBound ρ e j` refines the published
`HasOrbitWeightUpperBound`. If `r ≠ j` and `e j ≤ e r`, the orbit
coefficient `(ρ(g)) r j` vanishes on every scheme test. In particular,
it also rules out every other coordinate with exactly the original
line's cocharacter weight. This is not an irreducibility assertion.

`hasStrictOrbitWeightUpperBound_of_parabolic_eigenline` assumes a
smooth connected affine group, a cocharacter whose composite matrix
representation is the displayed diagonal, and represented dynamic
opposite-unipotent and parabolic subgroups with the parabolic preserving
the chosen line. On the actual opposite open cell, the opposite
unipotent has identity entries in all positions with row weight at
least column weight. Multiplying the preserved parabolic line therefore
gives zero at every other coordinate of at least the line weight.
The published opposite-cell open immersion is dominant because the
group is geometrically integral. Equality of this regular coefficient
with zero extends from the open cell to the group scheme, then to all
scheme tests by naturality. This follows the implemented proof of
`ParabolicEigenlineWeights`, retaining the equality-weight case.

For the quantitative statement, fix a connected reductive group,
maximal split torus `i`, generic cocharacter `ν`, and a torus-diagonal
representation with a line preserved by the minimal standard parabolic.
Let `χ_j` and `χ_r` be its actual torus characters, and set
`delta = χ_j - χ_r`. An **active** coordinate means that the indicated
orbit coefficient at the supplied scheme point is nonzero.

`orbitPairing_nonneg_of_simpleRootPairings_nonneg` proves
`<delta,d> ≥ 0` for every active coordinate and every cocharacter `d`
whose simple-root pairings are all nonnegative. For each natural `N`,
`N*d + ν` has strictly positive pairings on every simple root and
therefore defines exactly the minimal standard parabolic. The
published orbit upper bound gives
`N * <delta,d> + <delta,ν> ≥ 0` for every `N`. If
`<delta,d> ≤ -1`, the explicit choice
`N = (|<delta,ν>| + 1).toNat` contradicts this inequality. This
interior approximation avoids assuming that the line is preserved by
the larger parabolic of a boundary cocharacter.

Now let `α` be simple, `J = Δ \ {α}`, and let `zeta` be any standard
cocharacter for `J`, so that `m = <α,zeta> > 0`. Assume the same line
is preserved by `P_J`. For an active coordinate with `r ≠ j`, the
strict orbit bound gives the integer inequality `<delta,zeta> ≥ 1`.
For every dominant `c`, the cocharacter

```text
d = m * c - <α,c> * zeta
```

has nonnegative simple-root pairings, including zero pairing with `α`.
The preceding closed-chamber nonnegativity gives
`m * <delta,c> ≥ <α,c> * <delta,zeta> ≥ <α,c>`.
This is the precise conclusion of
`maximalParabolic_orbitPairing_gap`, with `delta` expressed by the
actual character-lattice equivalence. Inactive coefficients are zero;
no gap is asserted for the character of an inactive coordinate.

`exists_maximalParabolic_orbitPairing_gap` supplies every representation
and coordinate choice used in this argument from the structural group
hypotheses alone. It chooses a Chevalley representation with exact
all-test line stabilizer `P_J`, retains that eigenline in the simultaneous
torus diagonalization from `TorusEigenlineDiagonalization`, and derives
both parabolic line-preservation conditions from the actual subgroup
inclusions. The published `standardCocharacter` theorem supplies
`zeta`. Its positive root pairing and the universal quantitative gap
are conclusions. No line representation, highest-weight theorem,
irreducibility, orbit-gap, or analytic estimate is a premise of this
existence result.

The unit also proves
`HasTorusCharacterDiagonal.rationalMatrix_eq_diagonal`. It uses the
published `Langlands.Plancherel.rationalMatrix_eq_affineMatrix`,
`rationalPointEquiv_left`, and
`rationalCharacterEval_eq_affineUnitsEquiv` to specialize the universal
diagonal equation to actual identity-test rational points.

All algebraic results have an arbitrary field universe and allow both
characteristics and nonsplit connected reductive groups. The quantitative
existence theorem requires the ambient group to be affine and locally
of finite type; it uses the supplied actual maximal split torus,
generic cocharacter and simple root. Universal coefficient equations,
active-coordinate implications and the strict orbit bound retain
nonreduced scheme tests. The local-field norm conversion, compact
neighborhood comparison, II.3.5 open-cell conclusion and final
conjugation integral remain separate steps.
