# The Haar Hecke algebra inside the original distribution space

This definition unit realizes the published Haar Hecke algebra by its actual
densities, constructs the two actions on all algebraic distributions, and
defines the essentially compact submodules. It installs no new algebra carrier
or unproved algebra laws.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.12 Lemma and definition of H(G), printed pp.51–52 / PDF pp.57–58;
II.3.13 first Definition, printed p.53 / PDF p.59; second Definition and the
intersection on printed p.54 / PDF p.60.

`Distribution.heckeDistribution μ` is the composition of the existing
`Hecke.HeckeAlgebra.toTestFunction μ` and `Distribution.testDensity μ`.
It sends the actual function `h` to `f ↦ ∫ h(x)f(x) dμ(x)` in the full complex
algebraic dual. `heckeDistributionSpace μ` is precisely this linear map's range
as a submodule of that same dual. The original `HeckeAlgebra μ` supplies the
algebra and function carrier. Injectivity, compactness of the range, its equality
with the three uniform compact-distribution spaces, and compatibility with the
existing convolution product remain explicit statement obligations. The range
is not declared to be a new Hecke algebra.

For fixed `h : HeckeAlgebra μ`, `rightHeckeOperator μ h` is the transpose of
the test map `f ↦ convolution μ f (inversion h)`. Its value on `T` is denoted
`rightHeckeConvolution μ T h`. When μ is left Haar, the test kernel at `x` is
`∫ y, h(y)f(x*y) dμ(y)`: left Haar substitution in the published convolution
formula gives this expression. It is exactly `f * check(h μ)` in the source's
scalar-function convolution notation.

`leftHeckeOperator μ h` instead transposes
`f ↦ convolution μ.inv (inversion h) f`; its value is
`leftHeckeConvolution μ h T`. The inverse measure makes its test kernel
`∫ y, h(y)f(y*x) dμ(y)`, exactly `check(h μ) * f`.
Inversion of an arbitrary Haar density includes a modular factor when expressed
relative to the same left Haar measure. Using `μ.inv` implements that change of
measure directly, without imposing unimodularity or falsely identifying the
inverted distribution with the bare inverted density against μ. Mathlib's
`Measure.IsFiniteMeasureOnCompacts.inv` supplies the needed integrability
interface. The exact comparisons with the compact-distribution convolution,
scalar kernels and the source's displayed formulas remain later statements.

Both operators are actual complex-linear maps in `T`, obtained by precomposition
with the published test convolution maps. Their evaluation formulas are
definitional. These basic constructions only require μ to be finite on compact
sets; all source uses specialize to a left Haar measure. The construction does
not require every algebraic distribution to be a measure.

For a t.d. group, `rightEssentiallyCompact μ` consists of precisely those full
distributions for which `rightHeckeConvolution μ T h` lies in the published
`compactlySupported` submodule for every actual Hecke element h.
`leftEssentiallyCompact μ` is analogous, and `essentiallyCompact μ` is their
intersection. Their submodule proofs use linearity of these actual operators
and closure of the original compact-support submodule. No condition of membership
in the density range is substituted for the source's compact-support condition.
The product, compact-distribution inclusion, range-preservation statements,
completion comparison and categorical-center identification are not asserted
here. The categorical-center comparison will reuse the already published
`Distribution.IsConjugationInvariant` and its exact inner-action correspondence
`GroupAction.isConjugationInvariant_iff_fixed`; this unit adds no replacement
conjugation predicate.
