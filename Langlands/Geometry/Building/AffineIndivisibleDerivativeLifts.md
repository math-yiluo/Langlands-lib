# Integral affine models and indivisible derivative lifts

This module gives conditional affine arguments for the full derivative set.
It does not construct the affine roots of an actual quasi-split group.

`HasIntegralConstantDescription Ψ Φ x₀` says that an affine functional is in
`Ψ` precisely when its derivative belongs to `Φ` and its value at the chosen
origin `x₀` is an integer. There is no reducedness assumption on either set.
This is the coordinate form of the exceptional nonreduced model in the proof
of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
6.4.8, printed pp.225–226, PDF pp.256–257. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The registered 2024 corrections, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.32, do not change that proposition. They correct the separate
reductive-group reduction to use the adjoint group.

The implemented integer-model proof takes any full derivative and constructs
the affine functional with that derivative and value one at `x₀`. The defining
equivalence makes it a root. If its half were a root, integrality at `x₀`
would give an integer `n` with `2n = 1`, a contradiction. Thus the construction
retains derivatives whose halves are also in `Φ`. The auxiliary theorem
`mem_nonDivisibleRoots_of_apply_eq_one` isolates this arithmetic argument.
The reduced case follows directly from the Library equivalence between
reducedness and equality of the root set with its indivisible subset.

The transport statements are internal consequences of the Library definitions,
rather than additional classification results from the source.
`HasIndivisibleDerivativeLifts.of_comp` assumes root membership is detected by
pullback along an affine map. It pulls back a target derivative, chooses an
indivisible source lift, and descends that lift using its factorized linear
part. Affine functionals with that linear part descend after matching one
constant, even when the map is not surjective. Pullback commutes with halving,
so a half-root downstairs would contradict indivisibility upstairs.
`HasIndivisibleDerivativeLifts.transport` applies this argument to an affine
equivalence and the Library's `transportedRoots`.

All results apply to arbitrary real affine torsors and do not assume
affine-root-system axioms, finite rank, a characteristic, or a residue-field
condition. Applying them to actual quasi-split apartments still requires
proving the relevant root description or root-preserving comparison.
