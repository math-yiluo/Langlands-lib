# Chart families of a model over the thicker ring, and lifts of their transitions

Module `Langlands.AbelianScheme.ArtinianChartFamily` (namespace
`Langlands.AbelianScheme.ArtinianConstantCharts.Setting`). The two bases come from
`Setting R' R` in `ArtinianConstantCharts`.

## Models

`Model` is a scheme `Y` over `Spec R'` with a chosen base change `YS` to `Spec R` (maps `q`,
`pS` and the square `isPullback_q`) and a chosen special fibre `E` of `YS` over the residue field
(maps `iE`, `pE`, square `isPullback_iE`). For an open `U` of `Y`, `VT U = q⁻¹ U`; `resTo` is the
restriction of `q`, `isPullback_resTo` its base-change square and `liftVT` its universal property.
`agreeMod_of_resTo` and `resTo_eq_of_agreeMod` show that two maps out of an affine open of `Y`
agree after base change to `Spec R` if and only if they agree modulo the kernel of `φ`
(`AgreeMod`, module `TransitionObstruction`).

## Chart families

`ChartFamily M X e`, for a scheme `X` over `Spec R` and a map `e : E ⟶ X`, is a finite family of
affine opens `V l` of `Y` with open immersions `κ l : VT (V l) ⟶ X` over `Spec R` that equal `e`
on the special fibre. When `R` is local Artinian (so that `Spec R` has a single point), as in
`ArtinianConstantCharts`, the charts agree on points (`κ_apply_eq`), and `lift`, `θS` give
transition maps `θS l m : VT (V l) ⊓ VT (V m) ⟶ YS` that fix points, lie over `Spec R`, are the
inclusions on the diagonal and on the special fibre, and satisfy the cocycle condition
(`θS_pointwise`, `θS_base`, `θS_self`, `θS_fibre`, `θS_cocycle`). The definition allows families
whose opens and chart images cover only part of `Y` and `X`.

## Lifts

With `R` local Artinian, `ChartFamily.Lifts` consists of maps `θ l m : V l ⊓ V m ⟶ Y` over
`Spec R'` whose base change to `Spec R` is `θS l m` (`reduces`). They restrict to the inclusions on
the special fibre (`Lifts.fibre`). If `R'` is also Artinian, they fix points (`Lifts.pointwise`),
giving a `TransitionObstruction.Family` by `Lifts.family`. Separatedness over `Spec R'` makes the
triple overlaps affine, and the cocycle condition for `θS` yields the condition modulo the kernel
of `φ` for this family (`Lifts.agrees`).

For `Y` smooth and separated over an Artinian `R'`, `exists_lifts` gives lifts with `θ l l` the
inclusion. On each affine double overlap, `AffineNilpotentThickening.exists_lift` lifts
`θS l m ≫ q` along the nilpotent thickening.

## Provenance

SGA 1, Exposé III, §6, chooses local lifts and isomorphisms `f_ji` between them on the affine
overlaps (recomposed edition, arXiv math/0206203v2, printed pp. 64–66, PDF pp. 80–82). Here all
local lifts are opens of one model `Y`, and `θ l m` records the corresponding transition into
`Y` from the overlap, through chart `l`.
