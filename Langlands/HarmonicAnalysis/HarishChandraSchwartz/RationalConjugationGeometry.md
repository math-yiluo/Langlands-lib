# Actual geometry for the intrinsic conjugation integral split

This unit transports the proved geometric estimates of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, Proposition VIII.3.1, printed pp.323–325, to the
exact actual truncated cell used by `RationalConjugationSplit`.
The registered original is `waldspurger-2003-plancherel`, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The complement-height inequality is formula (2) on p.323; the
opposite-radical tail inclusion is on p.325. Their geometric input
is Lemma II.3.5, proved in `RationalOpenCellHeight`.

`RationalConjugationGeometricBoundsStatement` quantifies over the
actual connected reductive setup in arbitrary local-field universe,
with an affine locally finite type group, actual maximal split torus,
generic cocharacter, simple root `alpha`, and any standard cocharacter
`zeta` for `Delta \ {alpha}`. It retains an arbitrary nonempty finite
closed matrix realization `rho`, compact open Iwasawa subgroup `K`,
and a separate arbitrary compact open subgroup `H` of `G(F)`.
For `chi = zeta` followed by the actual torus inclusion, it proves
both of the following uniform estimates.

* There is `B > 0` such that, for every actual centralizer point `a`
  whose ambient value lies in the maximal-`alpha` root sector, and
  every `g` outside `rationalDynamicConjugationCell chi H a`,
  `1+height(a) <= B*(1+height(g)+height(a*g*a^-1))`.
* There is `b > 0` such that, for the same chamber sector and every
  actual opposite-radical point `u`, if `a^-1*u*a` is outside `H`,
  then `b*(1+height(a)) <= 1+height(u)`.

Every displayed height is the original `rationalHeight rho`. The
chosen `H` need not equal the Iwasawa compact `K`, and neither is
identified with the target's separate structural compact `K0`.
The theorem `rationalConjugationGeometricBounds` has exactly this
closed Prop as its type.

The transport begins with
`rationalParabolicSmallCell_eq_rationalDynamicConjugationCell`.
It takes the open subgroups `Gamma=H∩U` and `GammaBar=H∩V` with
their actual subgroup topologies. The geometric cell is
`a^-1 Gamma a M GammaBar`. The integration cell instead has
coordinates `g=m*u*v^-1` with
`a*(m*u*m^-1)*a^-1 ∈ H` and `v ∈ H∩V`. The proof gives both
coordinate changes explicitly. For a geometric factorization,
take the integration radical coordinate
`m^-1*(a^-1*gamma*a)*m` and opposite coordinate `v^-1`.
Conversely take `gamma=a*(m*u*m^-1)*a^-1` and `v^-1`.
Centralizer normalization of the radicals ensures that these
coordinates lie in the original actual subgroups. The group
identities recover exactly the two truncation conditions, so no
measure or almost-everywhere identification is used.

For the complement inequality,
`exists_rationalDynamicCell_complement_height_bound` pulls `H`
back to each closed actual radical. These pullbacks are open and
compact, so they satisfy the proved full II.3.5 theorem. The
published maximal-root-sector height comparison controls
`1+height(a)` by a constant times `1+order_alpha(a)`. Applying
`conjugationSigmaBound_of_openCellBound` gives the required
complement comparison for the geometric cell. The exact cell
equality transfers it to the integration cell, and increasing its
constant to `max(B,0)+1` makes the result strictly positive.

For the tail estimate,
`exists_rationalDynamicCell_opposite_tail_height_cutoff` applies
the proved `exists_rationalOppositeTail_height_cutoff` with the
same pullback `GammaBar=H∩V`. If inverse conjugation of `u` is
outside `H`, then `u` is outside `a*GammaBar*a^-1`, since every
point in the pullback has ambient value in `H`. This is exactly
the hypothesis of the already proved cutoff. It supplies the
second bound without adding a tail-height assumption.

All statements use the full actual chamber sectors in the common
norm kernel, include both local-field characteristics and nonsplit
groups, and retain all quantified compact and matrix choices. The
closed geometric statement supplies these two hypotheses of the
VIII.3.1 split. It does not claim the analytic constant-term or Xi
estimates, the tail integral bound, or the final closed intrinsic
cuspidal conjugation theorem.
