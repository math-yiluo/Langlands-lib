# Bounded finiteness of real Lie jump depths

Let `P : ParahoricBuildingData G` and `L : P.LieFiltrationData` be supplied
over a nonarchimedean local field `F` with the existing valuation and
topology instances. These results add no splitting, characteristic or
residue-characteristic assumption. The real-depth lattice and its strict
supremum are those in [KPLieFiltrationDual](KPLieFiltrationDual.md).
`lieJumpDepths x` is the set of real depths at which the strict piece is
strictly smaller than the non-strict piece. Under `L.IsPeriodic`, the strict
piece is the union over larger depths and is contained in the non-strict
piece, so the test is exactly their inequality in KP's definition of a jump.
No rationality premise is part of this set.

## Finite lattice values on a bounded interval

`finite_lieFiltrationReal_image_Icc` assumes `L.IsPeriodic` and finite
generation over `𝒪[F]` of the supplied nonnegative filtration at depth
zero at the point `x`. A genuine lattice at depth zero supplies this
finite generation; a spanning or freeness premise is not needed.

Write `A = 𝔤_{x,0}`. For nonnegative indices bounded by a natural number
`N`, monotonicity and repeated multiplication by the maximal ideal give the
bounds `𝔪^N • A ≤ 𝔤_{x,t} ≤ A`. This interval of
submodules is finite. The quotient of `A` by `𝔪^N • A` inside it is a finite
module over the finite ring `𝒪[F]/𝔪^N`: the maximal ideal powers have finite
quotients because the maximal ideal is finitely generated and the residue
field is finite. Every intermediate submodule is recovered by taking the
inverse image of its image in this finite quotient, so the map to
submodules of the quotient is injective.

For a real depth `r` in `[a,b]`, its natural ceiling shift `indexShift r`
is at most `indexShift a`. The shifted nonnegative depth is at most
`N = ⌈b⌉₊ + indexShift a`. By the definition of the real extension,
`𝔤_{x,r}` is determined by the shift and the lattice at this shifted
depth. Both coordinates range over finite sets, giving the real-depth
finiteness result without assuming a separate shift formula at negative
depths.

## Consequences for jumps

If `r < s` and `r` is a jump, the lattice at `s` is contained in the
strict piece at `r`, hence is strictly smaller than the lattice at `r`.
This gives `strictAntiOn_lieFiltrationReal_lieJumpDepths`, which holds even
without periodicity because the strict piece is defined by a supremum.
Under the bounded-value hypotheses this injectivity proves finiteness of
the jumps on each closed bounded interval. For a finite set `X` of
apartment points, with the depth-zero finite-generation hypothesis at
each member, the union of their jumps is again finite on every such
interval. `isClosed_and_isDiscrete_biUnion_lieJumpDepths` gives closedness
and discreteness in the real line for that union. The proof removes the
finitely many other points in a bounded neighborhood of each real number;
thus the set has no accumulation points.

## Source and scope

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), §13.3.1,
printed p. 470 / PDF p. 501, gives the real extension, strict piece and
periodicity (from Proposition 8.5.16, printed p. 319 / PDF p. 350, on
congruence models). The jump test and the chosen finite family of
representatives motivate the paragraph immediately before Example 13.4.3
(printed p. 473 / PDF p. 504). The finite-quotient proof here is a derived
argument, not the book's inference from local finiteness of the orbit set.
It works for any finite set of apartment points, optimal or not. To use
the result for the translates of chosen optimizers, one still needs
well-defined, conjugation-covariant lattices on the building. It is not a
discreteness result over all optimal points; the distinction is explained
by the [split type A₂ paper calculation](../../../notes/bruhat-tits/kp-optimal-depth-scope.md).
No actual integral models, left continuity, rationality of jump depths or
descent are proved here.

Registered sources: `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`, and
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
The corrections of 1 November 2024 (PDF pp. 37–38 and 49) do not change
these passages.
