# Lie filtration on the reduced building from compatible apartment data

Let `F` be a nonarchimedean local field (of either characteristic), `G` an
affine `F`-group scheme, and `P : ParahoricBuildingData G` supplied building
data. Write `A = P.Apartment`, `B = P.ReducedBuilding`, `𝒪 = 𝒪[F]` and
`𝔤 = GenericLie 𝒪[F] G`. Let `L : P.LieFiltrationData` be the supplied
nonnegative-depth Lie filtration on `A`.

`LieFiltrationData.IsAdjointCompatible` has two hypotheses:

- For `n ∈ N_G(S)(F)`, `x ∈ A` and `r ≥ 0`, the image of `L.lieFiltration x r`
  under `Ad(n)` equals `L.lieFiltration (n • x) r`.
- At every `x ∈ A`, `P.sharpFixer {x}` lies in `L.filtrationStabilizer x`.
  Thus each element of the subgroup used at `x` in the building quotient,
  and its inverse, preserve all the nonnegative-depth submodules at `x`.
  This does not identify the sharp fixer with the connected parahoric or
  the full `G(F)`-stabilizer.

Under these hypotheses `LieFiltrationData.lieFiltrationOnBuilding` defines
an `𝒪`-submodule of `𝔤` at each `y ∈ B` and `r ∈ ℝ`. On the chart `y = g •
P.apartmentMap x`, it is the image of `L.lieFiltrationReal x r` under `Ad(g)`.
To construct it, first extend both compatibility conditions to real depths:
`Ad(g)` is `𝒪`-linear and commutes with multiplication by every scalar in
`𝔪^⌈−r⌉₊`, where `𝔪` is the maximal ideal of `𝒪`. Applying the same
inclusion to the inverse gives equality. The resulting normalizer-equivariant
map on `A`, fixed at `x` by the sharp fixer, descends by `ApartmentQuotient.lift`
for the quotient (7.6.2). The chart formula and equivariance are consequences
of the lift, not choices of a representative.

`lieFiltrationPlusOnBuilding` is the supremum of these submodules over
`s > r`. It restricts to `L.lieFiltrationPlusReal` on the canonical apartment
and is adjoint-equivariant because submodule image preserves suprema. With
`L.IsPeriodic`, the real-depth filtration on each chart is decreasing;
`mem_lieFiltrationPlusOnBuilding` identifies the supremum with the union over
`s > r`, and `lieFiltrationPlusOnBuilding_le` includes it in the depth-`r`
submodule. The decreasing-family and union assertions are not made here for
arbitrary `L` without periodicity.

## Source and scope

This is a derived construction using Kaletha–Prasad, *Bruhat–Tits Theory: A
New Approach* (Cambridge, 2023), Remark 7.6.5 and (7.6.2), printed p. 266
(PDF p. 297), and §§13.3.1, 13.3.3–13.3.4, printed pp. 470–471 (PDF
pp. 501–502). KP defines the lattices as Lie algebras of integral models,
describes them on an apartment and obtains a parahoric model action. The
construction here uses supplied apartment submodules and explicit normalizer
and sharp-fixer compatibility instead. It neither constructs the models nor
proves either compatibility condition or periodicity for their Lie algebras.
It does not construct a graded action of the algebraic reductive quotient.
The authors' corrections of 1 November 2024, p. 49, do not change §13.3.
