# Global coordinates on a unit projective chart

Author: Worker 148.

This internal module uses arbitrary commutative rings `R` and `B` in universe
`u`, the polynomial ring `A = R[X_0, ..., X_n]` with its standard grading `𝒜`
and irrelevant homogeneous ideal `I`, and an arbitrary scheme `X` in universe
`u`. Its proofs derive from localization, the existing global-coordinate chart
formula, the Gamma-Spec adjunction and coordinate-ratio generation.

The algebraic definition `unitChartRingMap` takes any ring homomorphism
`f : A → B`, any element `t : A`, and a witness `IsUnit (f(t))`. It maps
`Away 𝒜 t → B` by including into `A[t⁻¹]` and then using the localization
lift of `f`. No homogeneity or positive-degree condition is needed for this
ring map. `chartRingMap_eq_unitChartRingMap` identifies its composite with
`B → B[(f(t))⁻¹]` with the existing localized chart evaluation. The proof
compares ring maps out of `A[t⁻¹]` on `A`.

The geometric comparison `fromOfGlobalSections_eq_unitChart` additionally
requires `f : A → Γ(X, ⊤)`, an explicit unit-ideal witness
`I.toIdeal.map f = ⊤`, a degree `d > 0`, a homogeneous element `t ∈ 𝒜 d`,
and a unit-image witness `IsUnit (f(t))`. The unit-ideal premise defines the
actual global map to Proj; positive-degree homogeneity defines its projective
chart. A unit global section has the whole scheme as its basic open, so the
proof cancels that open immersion in the local chart formula. The resulting
actual scheme morphism is `X.toSpecΓ`, followed by `Spec.map` of
`unitChartRingMap`, followed by the chart open immersion. A unit image alone
without positive-degree homogeneity is not a projective-map existence
condition. Although a positive-degree homogeneous element with unit image
implies the unit-ideal property mathematically, Lean explicitly passes that
property to `Proj.fromOfGlobalSections`.

`toSpecΓ_specMap_eq_iff` uses the Gamma-Spec adjunction to detect equality
of affine-target morphisms by equality of the ring maps into global sections.
`fromOfGlobalSections_eq_iff_unitChart` applies this to two maps `f` and `g`
on the same arbitrary scheme `X`. It retains both explicit unit-ideal witnesses,
a common homogeneous `t` of degree `d > 0`, and both unit-image witnesses.
Under these premises, the actual maps to Proj are equal if and only if their
unit-chart ring maps are equal. The proof cancels the common chart open
immersion after applying the geometric formula.

For `t = X_j`, `unitChartRingMap_ratio_mul` needs only a ring map `f : A → B`
and a unit image of `X_j`. It evaluates the degree-one ratio `X_i/X_j` and
proves that multiplying its value by `f(X_j)` gives exactly `f(X_i)`. The
proof evaluates the fraction using a unit inverse; no field or reducedness
hypothesis is used.

The coefficient and extensionality lemmas assume an algebra structure of `B`
over `R`. Each supplied ring map must send `C(r)` to `algebraMap R B r`.
`unitChartRingMap_algebraMap` records that this coefficient map is retained.
`unitChartRingMap_ext` assumes unit images of the same variable `X_j`, both
coefficient conditions, and equality on every ratio `X_i/X_j`. Since these
ratios generate the affine chart as an algebra over `R`, algebra-adjoin
induction proves equality of the whole chart ring maps. Ratios alone are not
asserted to determine ring maps with different coefficient maps.
