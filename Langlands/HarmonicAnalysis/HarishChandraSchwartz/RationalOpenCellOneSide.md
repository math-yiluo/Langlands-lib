# The actual one-sided open-cell height estimate

This unit proves steps (2) and (3) of Waldspurger, *La formule de
Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
Lemma II.3.5, printed pp.257–259. The registered original is
`waldspurger-2003-plancherel`, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The conclusion is the one-sided inclusion `g ∈ GammaBar * P` under
smallness of the height of `g` and its chamber conjugate. The last
combination of opposite parabolics in II.3.5 is a separate step.

`RationalOneSidedOpenCellHeightStatement` quantifies over an arbitrary
nonarchimedean local field in universe `u`, an affine locally finite
type connected reductive group, its actual maximal split torus `i`
and generic cocharacter `nu`, and any simple root `alpha`. For the
maximal face `J = Delta \ {alpha}`, it allows any standard
cocharacter `zeta`. Its dynamic opposite radical is the radical
opposite to `P_J`. The other choices are any nonempty finite closed
matrix realization `rho`, any compact open subgroup `K` satisfying
the minimal Iwasawa decomposition `G(F) = P_0(F) K`, and any compact
open subgroup `GammaBar` of that opposite radical. It concludes that
there is one `C > 0` such that, for all actual points `a` of the full
minimal chamber and all `g ∈ G(F)`,

```text
1 + height_rho(g) + height_rho(a*g*a^-1)
    <= C * order_alpha(a)
```

implies `g ∈ GammaBar * P_J(F)`. No restriction to the uniformizer
section or the common norm kernel appears. The actual subgroup
`GammaBar` is mapped by its inclusion into `G(F)` in the conclusion.
The theorem `rationalOneSidedOpenCellHeight` has exactly this closed
Prop as its type.

`rationalTorusCharacterOrder` extends the torus character order to
an ambient function using `Function.invFun` of the actual point
inclusion. The function is used only on the torus image. The proof
of `rationalTorusCharacterOrder_map` uses monicity of the torus
inclusion to identify its value with the actual order there. Hence
the right-hand side above is the source's simple-root coordinate
on every chamber point; values away from that image play no role.

The implemented compact-set step,
`exists_mem_opposite_open_of_small_conj_on_compact`, first constructs
the exact maximal-parabolic eigenline representation and its
simultaneous torus-character basis using the proved
`exists_maximalParabolic_orbitPairing_gap`. The exact all-test
stabilizer gives both parabolic line-preservation conditions. All
six hypotheses of `mem_of_coordinate_bounds` are then supplied by
`RationalParabolicOrbitCoordinates`: the uniform exponential upper
bound in the original matrix height; a positive compact-set lower
bound; exponential growth under actual full-chamber conjugation;
common positive scalar multiplication by a parabolic point;
distinguished coordinate exactly one on the opposite radical; and
small off-line coordinates forcing membership in the given open
subgroup. The growth constant is `log(q)/<alpha,zeta> > 0`.
The resulting lemma works for any real function `sigma` dominating
the original matrix height. Its proof retains no coordinate or
analytic estimates as assumptions.

For the density extension, the proof sets
`sigma = rationalCompactHeight rho K`. This is the already proved
real compact-biinvariant envelope of the original height. It is
nonnegative, subadditive, invariant under inversion, exactly left
`K` invariant, and locally constant together with its conjugate.
The proved actual II.3.3 bound in `RationalChamberContraction` and
the uniform envelope comparison give the same parabolic contraction
bound for this auxiliary height, with a larger constant at least
one. The minimal Iwasawa decomposition gives `g = k*p` with
`p ∈ P_0(F) <= P_J(F)`, in the order needed by the generic lemma.

`dense_oppositeUnipotent_mul_parabolic` proves the remaining actual
density input. The published actual dynamic open-cell conullness
proof applies to a chosen Haar measure on `G(F)`; positivity on
nonempty open sets makes the cell dense. Inversion transports this
density from the `P * Ubar` cell to the `Ubar * P` product. The
parabolic is closed because it is represented by a closed subgroup
scheme. The image of `GammaBar` is compact, so `GammaBar * P` is
closed. These inputs and the compact-set step discharge every
hypothesis of `mem_mul_of_dense`. The resulting theorem is
`exists_mem_opposite_open_mul_of_small_compactHeight`.

Finally,
`exists_mem_opposite_open_mul_of_small_rationalHeight` eliminates
the auxiliary envelope. If its additive comparison constant is
`2*D`, then

```text
1 + envelope(g) + envelope(a*g*a^-1)
  <= (1 + 4*D) * (1 + height_rho(g) + height_rho(a*g*a^-1)).
```

Dividing the preceding positive constant by `1 + 4*D` gives the
closed result for the supplied original matrix realization. This
is the reason the proof needs neither a compact-adapted matrix
embedding nor equality of any auxiliary and original height.

The one-sided result is proved in arbitrary universe, allows both
local-field characteristics and nonsplit groups, and is vacuous
when there is no simple root to choose. It assumes only the stated
Iwasawa factorization and compactness choices for this prerequisite.
It does not prove the two-parabolic II.3.5 inclusion, the
opposite-radical tail cutoff, or the VIII.3.1 integral theorem.
