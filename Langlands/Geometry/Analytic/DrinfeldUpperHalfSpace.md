# Drinfeld's upper half space

Author: Worker 21.

This module constructs Drinfeld's upper half space `Ω` of dimension `d` as a
subspace of the analytic affine space of `AnalyticAffineSpace`. `Ω` consists of
the points at which no nonzero `F`-rational affine-linear function vanishes.
The module proves that every point of `Ω` has a rational domain of a closed
polydisc as a neighborhood inside `Ω`, that `Ω` is open, and equips `Ω` with an
indexed affinoid atlas and an atlas presentation. It also adds affine-linear
functions on the affine space and their absolute values.

Declarations about affine-linear functions lie in
`Langlands.Analytic.AnalyticAffineSpace`; the upper half space lies in
`Langlands.Analytic.DrinfeldUpperHalfSpace`.

## Original sources

- Drinfel'd, *Coverings of p-adic symmetric regions*, Functional Analysis and
  Its Applications 10 (1976), registered as
  `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
  `7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`, opening
  paragraph, printed p.107 / PDF p.1: "Let K be a local non-Archimedean field,
  d a natural number, and Ω^d the set of points P^{d-1}_K, not lying on any
  hyperplane defined over K. Ω^d is a strict analytic space over K, on which
  PGL(d, K) acts".
- Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper
  half spaces; elaboration of Carayol's program*, Invent. Math. 129 (1997),
  registered as `harris-1997-drinfeld-cohomology`, §2, printed p.88 / PDF p.14:
  "Let Ω be Drinfel'd's generalized upper half space of dimension n over F
  [Dr]: Ω is the rigid-analytic space over F whose points over `\bar{ℚ}_p` are
  given by `ℙⁿ(\bar{ℚ}_p) − ⋃ H(\bar{ℚ}_p)`, where H runs over the set of
  F-rational hyperplanes in `ℙⁿ`."
- Harris, *Galois properties of cohomological automorphic forms on GL(n)*
  (1999), registered as
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2, printed
  p.303 / PDF p.5: for the `GL(n)` application `Ω` has dimension `n − 1`
  ("we may take `D = 2 dim U(ẽ) = 2(n − 1)`").

Notation. The source fields are renamed: Drinfeld's local field `K` and
Harris's `F` are `F` here, and `K` here is the complete field over which the
analytic spaces are built. The dimension is `d`, so this `Ω` is Drinfeld's
`Ω^{d+1}` and Harris's `Ω` of dimension `n = d`. The `GL(n)` application uses
`d = n − 1`.

Derived choices.

- Points are Berkovich points of the glued affine space over `K` (bounded
  multiplicative seminorms on the polydisc algebras), not rigid points.
  "Not lying on a hyperplane" is read as "the absolute value of its linear
  form is nonzero at the point".
- The F-rational hyperplane `Z₀ = 0` at infinity is removed first: `Ω` is
  described inside the affine chart `Z₀ ≠ 0`. There the F-rational hyperplanes
  are the zero sets of `a₀ + Σᵢ aᵢ₊₁ Tᵢ` with `(a₀, …, a_d) ∈ F^{d+1}` not of the
  form `(a₀, 0, …, 0)`, and the forms with only `a₀ ≠ 0` never vanish. So the
  quantification over all nonzero coefficient vectors gives exactly the
  complement of the F-rational hyperplanes in `ℙᵈ`.
- `F` is any nontrivially normed field whose closed balls are compact
  (`ProperSpace F`); local fields are examples. `K` is a complete, nontrivially
  normed, ultrametric normed `F`-algebra. The sources take `K = F` or an
  extension such as the completed maximal unramified extension.
- The atlas is the one forced by the gluing construction: charts are rational
  domains of closed polydiscs contained in `Ω`. It is not Drinfeld's affinoid
  covering by the inverse images of simplices of the building, and the
  strictness of `Ω`, the `PGL` action and the formal model are not treated.

## Affine-linear functions

From here `K` is a nontrivially normed, ultrametric field (and complete where
gluing is used), and `c : Fin (d + 1) → K`.

- `linearForm K d m c = c₀ + Σᵢ cᵢ₊₁ Tᵢ` in the `m`-th polydisc algebra, and
  `linearSeries K d m c` is the same expression as a power series;
  `presentationMap_linearSeries` identifies its class with `linearForm`.
- `restriction_linearForm`: radius restriction preserves `linearForm`.
- `linearForm_sub` and `linearForm_smul`: the form is additive in `c`, and
  `ℓ_{t • c} = t · ℓ_c`.
- `linearNorm K d c` is the continuous function `z ↦ |ℓ_c(z)|` on the glued
  space, well defined by `linearForm_glued` (`linearNorm_chart`,
  `continuous_linearNorm`).
- `linearForm_le`: on the `m`-th polydisc, if all `‖cᵢ‖ ≤ B` then
  `|ℓ_c| ≤ (d + 1) B ‖ϖ‖⁻ᵐ`. It uses subadditivity of the seminorm,
  `|cᵢ| · |Tᵢ| ≤ B ‖ϖ‖⁻ᵐ`, and `1 ≤ ‖ϖ‖⁻ᵐ`.

## The upper half space

`coefficients F K d a` is the image in `K^{d+1}` of `a ∈ F^{d+1}`.

```
Omega F K d = {z | ∀ a : Fin (d + 1) → F, a ≠ 0 → |ℓ_a(z)| ≠ 0}.
```

The rational domains used as charts are built from Laurent charts.
`laurentChart K d M c r hr` is the existing rational chart over the `M`-th
polydisc with denominator `ℓ_c`, single numerator `1` and radius `r⁻¹`. The
numerator `1` gives unit-ideal generation, and `mem_locus_laurentChart` shows
its locus is `{y | r ≤ |ℓ_c(y)|}`. `laurentInter` intersects these charts over
a list of coefficient vectors with the existing `RationalChart.inter`, starting
from `RationalChart.whole`. `mem_locus_laurentInter` describes its locus as
`{y | r ≤ |ℓ_c(y)| for all c in the list}`.

`shell F d c = {a | ‖c‖⁻¹ ≤ ‖a‖ ≤ 1}` for a fixed `c ∈ F` with `1 < ‖c‖`, with
the sup norm on `F^{d+1}`. It is compact (`isCompact_shell`), does not contain
`0`, and every nonzero vector has a nonzero multiple in it
(`exists_smul_mem_shell`, from Mathlib's `rescale_to_shell`).

`exists_rational_nhds` is the main theorem. Every `z ∈ Ω` has `M` and a
rational chart `R` of the `M`-th polydisc such that the image of its locus
contains `z`, is contained in `Ω` and is a neighborhood of `z`. Proof:

1. `z` lies in the `m`-th polydisc; put `M = m + 1` and `ρ = ‖ϖ‖⁻ᴹ`.
2. `a ↦ |ℓ_a(z)|` is Lipschitz on `F^{d+1}` (by `linearForm_le` and the reverse
   triangle inequality) and positive on the shell. By compactness it has a
   minimum `δ > 0` on the shell.
3. Take a finite `η`-net `T` of the shell with `η = δ / (2 (d + 1) ρ)`, and
   let `R` be the intersection of the Laurent charts `{y | δ/2 ≤ |ℓ_b(y)|}`,
   `b ∈ T`, of the `M`-th polydisc.
4. `R ⊆ Ω`: for `a ≠ 0` choose `t ≠ 0` with `t • a` in the shell and `b ∈ T`
   with `‖t • a − b‖ < η`. Then `|ℓ_{t•a}(y)| ≥ |ℓ_b(y)| − |ℓ_{t•a−b}(y)| >
   δ/2 − (d + 1) η ρ = 0`, and `|ℓ_{t•a}(y)| = |t| |ℓ_a(y)|`.
5. `z ∈ R`, since `|ℓ_b(z)| ≥ δ > δ/2` and restriction preserves the forms.
6. `R` is a neighborhood of `z`: the open set of points of the open disc
   `|Tᵢ| < ρ` with `|ℓ_b| > δ/2` for all `b ∈ T` contains `z` and lies in
   `R`.

`isOpen_omega` follows: `Ω` is open in the affine space.

From here `NeZero d` is assumed, as for the atlases of the affine space.

- `isOriginalChartDomain`: `Ω` satisfies the existing
  `IsOriginalChartDomain` condition for the rational atlas
  `AnalyticAffineSpace.rationalAtlas K d`. The single chart from
  `exists_rational_nhds` is a member of that atlas
  (`DirectedRationalAtlas.atlas_ofChart_range`).
- `atlas F K d : IndexedAffinoidAtlas.{u, u, u} K (Omega F K d)` is the existing
  `subspaceAtlas` of the rational atlas on `Ω`: its charts are the rational
  domains of closed polydiscs contained in `Ω`, with their original algebras
  and restrictions.
- `presentation F K d : AffinoidAtlasPresentation.{u, u, u} K` is `Ω` with this
  atlas.

## Scope

Not constructed here: the action of `GL(d + 1, F)` (or `PGL`), the reduction
map to the Bruhat-Tits building, Drinfeld's coverings, and any comparison with
the rigid-analytic space or the formal model.
