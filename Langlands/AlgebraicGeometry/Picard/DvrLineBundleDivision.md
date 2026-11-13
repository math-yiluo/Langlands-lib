# Dividing line-bundle sections by the uniformizer over a DVR

Author: Worker 171.

Module `Langlands.AlgebraicGeometry.Picard.DvrLineBundleDivision`, namespace
`Langlands.AlgebraicGeometry.Picard.DvrAbelianGeometry`.

- `chartE_injective`, `chartE_zero`: properties of the published chart coordinates
  `SectionClearing.chartE` of sections of a module trivialized on an open `T`.
- `basicOpen_chartE_le`: the principal open of the chart coordinate of a global
  section lies in its generation open (the coordinate restricted there is a unit;
  published `QuasiAffineSectionBasis.le_trivializationOpen_of_chart_unit`).
- `exists_eq_unifX_smul`: for an abelian scheme `A` over a discrete valuation domain,
  irreducible `π` and a line bundle `L` on the total space, a global section of `L`
  whose generation open contains no point of the special fibre equals
  `unifX A π • s₁` for a global section `s₁`. In each local trivialization the
  coordinate has principal open inside the generation open, so it misses the special
  fibre and `exists_eq_unifRes_mul` divides it; the local quotients `chartF` agree on
  overlaps (`unifRes` is a nonzerodivisor) and glue in the sheaf of `L`.
- `exists_specializes_closedPoint`: every point specializes to a point of the special
  fibre (the structure morphism is closed and the closed point lies in the closure of
  every point of `Spec R`).
- `not_forall_unifX_pow_smul`: a global section with nonempty generation open is not
  divisible by every power of `unifX A π`. Choose a point `y` of the generation open,
  a special point `x` with `y ⤳ x` and a trivialization around `x`; the chart
  coordinate is divisible by all powers, hence zero by
  `eq_zero_of_forall_unifRes_pow_dvd`, so the section restricts to zero there, and the
  pulled-back section (`openSection_restriction`, `trivializationOpen_zero`,
  `lineBundlePullbackSectionOpen`) would have empty generation open containing `y`.

Internal infrastructure derived from published Library and Mathlib results; no
external source is asserted.
