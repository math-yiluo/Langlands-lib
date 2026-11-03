# Chamber Iwahori and full central-factor multiplication maps

This module defines the chamber subgroup `I_C = P_C` on the published
`ParahoricBuildingData G`. It also defines multiplication maps for its
negative, full central, and positive factors. The maps take values in
the actual group `G(F)`; no range or injectivity claim is part of these
definitions.

The sources are Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
and the corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`.

- Definition 7.4.1(4), printed p. 255 / PDF p. 286, defines
  `P_Ω = Z(F)^0 G(F)^sharp_Ω`. Definition 7.4.5(2), printed p. 256 /
  PDF p. 287, calls `P_C` the Iwahori subgroup for a chamber `C`.
- Proposition 7.3.12(3),(5), printed pp. 250–251 / PDF pp. 281–282,
  and Corollary 7.4.9, printed p. 257 / PDF p. 288, supply the
  sharp-group products motivating the maps. Passing to the full
  parahoric replaces the sharp central factor by `Z(F)^0`; the
  resulting decomposition is a separate statement.
- Definition 7.3.3(1) and Remark 7.3.4, printed p. 247 / PDF p. 278,
  require the block `U_{a,x,f(a)} U_{2a,x,f(2a)}`. The imported
  `ChamberRootProducts` definitions retain this factor, with a trivial
  second factor when `2a` is not a relative root.
- Fact 7.4.6 and Corollary 7.4.9, printed pp. 256–257 / PDF
  pp. 287–288, explain the mixed facet depths and the necessary choice
  of positive roots.

The corrections, PDF pp. 33–35, were checked. They add corrected AS5
to Chapter 7, add a separate strict-depth arbitrary-order assertion to
7.3.12, and correct the notation after Definition 7.4.1, the example
in Remark 7.4.2, and the function subscript in Lemma 7.4.4(2).
None changes the definitions or multiplication formulas used here.
This module asserts no structural conclusion requiring those axioms.

The inputs are a nonarchimedean local field `F` with its published
valuation and topology instances, an affine `F`-group scheme `G`, and
`P : ParahoricBuildingData G`. The latter contains the connected
reductive structure, maximal split torus `i : S → G`, actual root
valuations and apartment, centralizer `j : Z_G(S) → G`, and the
actual data of KP Definition 2.6.23 for `Z(F)^0` and `G(F)^0`.
The definition does not assert existence or choice independence of
these data.

`P.chamberIwahori C` is exactly `P.parahoric C`, hence the join of
the image of the actual `Z(F)^0` and the actual sharp root-generated
group. It is defined for every subset for totality; the term
“Iwahori” applies when `C` is an actual apartment chamber.

`P.iwahoriUnipotentPoints ν C` is the intersection of this full
subgroup with
`(Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ P.i)).carrier`
evaluated at `Spec F`. Under `IsGenericCocharacter P.i ν`, this is
the actual unipotent radical of the chosen minimal parabolic,
intersected with `I_C`. Replacing `ν` by `-ν` selects the opposite
radical. No genericity is required merely to define the intersection.

The three multiplication maps are internal notation derived from the
displayed source products:

- `iwahoriUnipotentProduct C ν` multiplies a negative intersection
  element, an element of the actual `P.centralizerZero`, and a
  positive intersection element.
- `orderedIwahoriChamberProduct x strict aneg apos` uses the imported
  point blocks, at depth `0` for `strict = false` and depth `0+` for
  `strict = true`, on both sides of `P.centralizerZero`.
- `orderedIwahoriFacetProduct Fa aneg apos` uses facet blocks at
  negative depth `0+` and positive depth `0`, with the same full
  central factor.

In each map the central element is a rational point of `Z_G(S)` and
is sent into `G(F)` by `rationalPoints.map P.centralizer.j`.
Ordered block products use `List.ofFn` and `List.prod` in their
`Fin n` index order. The indexing functions are arbitrary here.
Structural targets must require that each enumerate all indivisible
roots of its specified sign without repetition.

These definitions do not identify `I_C` with the sharp subgroup,
identify `Z(F)^0` with a sharp centralizer, assert product bijections,
or assert compactness or openness. Those remain statement targets
with explicit source hypotheses. This chamber Iwahori is distinct
from the smaller simultaneous normal compact-open basis used in
Renard V.5.2.
