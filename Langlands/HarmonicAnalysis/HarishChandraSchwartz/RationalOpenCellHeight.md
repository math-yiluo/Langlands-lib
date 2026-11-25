# The actual maximal-parabolic open-cell height estimate

This module proves the actual-point form of Waldspurger, *La formule
de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
Lemma II.3.5, printed pp.257–259. The original is registered as
`waldspurger-2003-plancherel`, DOI
[10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
The source's final two-parabolic intersection argument is on p.259.

`RationalParabolicOpenCellHeightStatement` has the following choices:
an arbitrary nonarchimedean local field in universe `u`; an affine
locally finite type connected reductive group; its actual maximal
split torus `i` and generic cocharacter `nu`; a simple root `alpha`;
any standard cocharacter `zeta` for `J = Delta \ {alpha}`; any
nonempty finite closed matrix realization `rho`; a compact open
subgroup `K` with the minimal Iwasawa factorization `G(F)=P_0(F) K`;
and arbitrary compact open subgroups `Gamma` and `GammaBar` of the
actual dynamic radicals `U(zeta)(F)` and `U(-zeta)(F)`.

For those choices it proves that there is `C > 0` such that, for
every actual point `a` of the full minimal chamber and every
`g ∈ G(F)`,

```text
1 + height_rho(g) + height_rho(a*g*a^-1)
    <= C * order_alpha(a)
```

implies `g ∈ a^-1 Gamma a M GammaBar`. Here
`M = Z_G(zeta)(F)`. The set is defined by
`rationalParabolicSmallCell` in exactly that unipotent-first
coordinate order: `g = (a^-1*u*a)*m*v`, with `u ∈ Gamma`,
`m ∈ M`, and `v ∈ GammaBar`, all read in the ambient rational
points. `rationalTorusCharacterOrder` is the extension from
`RationalOpenCellOneSide`; on every chamber point it is the actual
simple-root character order. `OpenCellBound` expresses precisely
the displayed uniform implication. The theorem
`rationalParabolicOpenCellHeight` has this closed Prop as its type.

The first one-sided implication is imported from
`exists_mem_opposite_open_mul_of_small_rationalHeight` in
`RationalOpenCellOneSide`. That theorem constructs the parabolic
line coordinates, proves the actual compact-set step, extends it
by actual cell density and closedness, and returns from an
auxiliary compact-invariant height to the supplied original matrix
height. All of its hypotheses here are among the quantified choices
above. There is no coordinate or analytic estimate left as a premise.

To obtain the other one-sided implication with the same `K`,
`IsIwasawaPair.map_conj` first proves a group-theoretic fact:
`G = P K` implies `G = (w P w^-1) K` for every `w`. Factor
`w^-1 = p0*k0`; then `w P w^-1 = k0^-1 P k0`, and factoring
`k0*g` in `P K` gives the required factorization of `g`.
`isIwasawaPair_minimal_neg` applies this lemma to the proved actual
rational chamber conjugacy in
`MinimalParabolicDistanceLength.exists_map_conj_eq`, followed by the
standard minimal-parabolic endpoint identities. Thus opposite
Iwasawa is a conclusion for the original `K`, with no extra
compact choice or premise.

The reversed simple roots are the negatives of the original ones.
`simpleRoot_maximalFace_neg` identifies their maximal faces exactly,
and `IsStandardCocharacter.neg` makes `-zeta`
standard for the reversed face. Inversion carries the entire actual
chamber to the reversed chamber. Simultaneous root negation and
point inversion preserve the character order, as proved in
`rationalTorusCharacterOrder_neg_inv_map`. Applying the one-sided
result to these reversed data gives
`exists_mem_open_mul_opposite_of_small_rationalHeight`: small
`height(g) + height(a^-1*g*a)` forces `g ∈ Gamma * Pbar`.

For the final intersection, apply the original one-sided result to
`g^-1`, and the reversed result to `a*g*a^-1`. Inversion invariance
of the original height leaves the same smallness expression in
both applications. The constant is the minimum of the two positive
one-sided constants. Membership in the actual torus centralizer
ensures that conjugating `Gamma` by `a^-1` stays in `U` and that
`a` lies in both parabolics. The pointwise argument in
`mem_rationalParabolicSmallCell_of_opposite_memberships` then uses
`P(chi) ∩ P(-chi) = Z(chi)` on actual points: after removing the two
radical factors, the remaining element is in both parabolics and
therefore in `M`. This proves the asserted cell inclusion without
an intersection hypothesis.

The result includes both local-field characteristics, nonsplit
connected reductive groups, chamber walls and the original arbitrary
closed matrix realization. A choice of simple root is impossible
in relative rank zero, so this prerequisite is vacuous there; the
separate rank-zero compactness result remains available for VIII.3.1.
This module proves II.3.5. It does not prove the tail cutoff, the
constant-term estimates, or the final VIII.3.1 integral theorem.
