# Scalar-compatible relative weighted restricted series

Author: Worker 56.

Let `r` be a positive real polyradius on a variable type `σ`, and let `A`
be an ultrametric normed commutative ring. This file equips the existing
actual weighted restricted series `GeneralizedTateAlgebra r A` with
scalar structures over a common base and with bounded algebra maps.
It retains the existing coefficients, convolution multiplication and
weighted Gauss norm.

For any commutative semiring `R` and `Algebra R A`,
`instAlgebraOfAlgebra` inherits the `R`-algebra structure from the
weighted restricted subalgebra of `MvPowerSeries σ A`.
`instIsScalarTower` proves the compatible scalar tower
`R → A → GeneralizedTateAlgebra r A`. The scalar action is coefficientwise,
as recorded by `series_smul`; `series_algebraMap` identifies the base
algebra map with the constant series whose coefficient is `algebraMap R A c`.
These instances use Mathlib's inherited subalgebra structures. The new
algebra instance has priority 500, preserving the existing instance over
the coefficient ring itself; their coefficient-ring specializations
agree definitionally.

If `K` is a normed field and `A` is a normed `K`-algebra,
`instNormedAlgebraOfNormedAlgebra` makes the weighted series a normed
`K`-algebra. For every exponent `d`, its proof uses

\[
\|c a_d\|r^d\leq \|c\|\,\|a_d\|r^d
                 \leq \|c\|\,\|f\|.
\]

The published coefficient characterization of the weighted Gauss norm
then gives `‖c • f‖ ≤ ‖c‖ * ‖f‖`. The instance has priority 500 and its
algebra structure is the one just constructed. When the coefficient ring
is the base field, it agrees definitionally with the existing
coefficient-specific normed algebra instance.

The remaining constructions require only `Algebra K A`, not
`NormedAlgebra K A`, in addition to the normed-field and ultrametric
normed-ring hypotheses. `constantAlgHom r K A` bundles the actual
coefficient inclusion as a bounded `K`-algebra map
`A → GeneralizedTateAlgebra r A`. The inherited scalar tower supplies its
scalar compatibility, and the published constant-series norm equality
supplies bound one. `norm_constantAlgHom` and
`isometry_constantAlgHom` prove norm preservation and isometry.

For a bounded `K`-algebra map `φ : B → D`,
`mapCoefficientsAlgHom r φ` bundles the published coefficientwise series
map as a bounded `K`-algebra map between the corresponding relative
series algebras. Its algebra-map compatibility follows from the
constant-series formula and scalar compatibility of `φ`.
`norm_mapCoefficientsAlgHom_le` transfers every supplied nonnegative
bound `C` unchanged:
if `‖φ b‖ ≤ C * ‖b‖` for every `b`, then
`‖mapCoefficientsAlgHom r φ f‖ ≤ C * ‖f‖`.
The bundled maps respect identity and composition. The final naturality
identity says that including coefficients and then mapping series equals
mapping coefficients and then including them. These identities are
proved by extensionality from the actual coefficientwise maps.

The source motivation is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), Definition 2.1.6(i), printed/PDF page 8,
read directly. That definition constructs relative finite-variable
weighted restricted series over a `k`-affinoid algebra with the weighted
coefficient norm. Registered original:
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
retained at
`/home/taskhub/central-library/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009/Berkovich--Non-archimedean analytic spaces (Trieste lectures)--2009.pdf`.

The scalar structures and map laws here are derived from that series
formula, the published weighted series and coefficient-map constructions,
and Mathlib's subalgebra and formal-series algebra structures; they are
not a separately quoted theorem of the source. As in the imported
definitions, weighted decay uses the cofinite filter on finitely supported
exponents. In finitely many variables this is the source's decay with
total degree. The implementation also permits arbitrary variable types
and ultrametric normed commutative coefficient rings. It needs neither
completeness nor coefficient nontriviality, a norm-one condition, or a
value-group condition on the positive radii. The base field in the
normed-algebra and bounded-map sections is a `NormedField`; it need not
separately be assumed ultrametric.

This unit supplies actual scalar-compatible relative series and maps.
Relative quotient comparison, surjectivity on series, independence of
affinoid presentation, and analytic domains and sites remain separate
obligations.
