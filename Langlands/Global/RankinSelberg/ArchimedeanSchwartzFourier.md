# Exact Fourier products from the rectangular measure comparison

This internal module proves a conditional Fourier formula for the restricted
adelic tensor constructed in `ArchimedeanSchwartzAssembly`. Its entry proposition
is
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor.RestrictedTensorFourierReductionStatement`,
and `restrictedTensorFourierReduction` proves that proposition. The retained
premise is the published `RectangleTateStatement`; this module does not prove that
measure comparison or the full `ArchimedeanFactorizationStatement`.

The result is implementation infrastructure derived from the published coordinate,
character, tensor and integral definitions. It is not a new translation from an
original source. The names below are in the namespace
`Langlands.Global.RankinSelbergGlobal.EqualSchwartzTensor` unless specified.

## Statement and conventions

Assume `RectangleTateStatement`. Let `F` be a number field with compact
`AdeleQuotient F`, and let `ψ` be a unitary additive character of its adeles, trivial
on the diagonal copy of `F`. Let `S` satisfy `FiniteAdditiveSupport ψ S`. Supply
real and complex scales `aR`, `aC` satisfying the published
`IsRealAdditiveComponent` and `IsComplexAdditiveComponent` conditions, canonical
finite characters `ψv`, and finite additive Haar measures `νv` self-dual for those
characters.

For every natural number `n`, real and complex families of Schwartz functions
`ΦR`, `ΦC`, and a family of finite local functions `Φv`, let
`Φ = restrictedTensor F n S ΦR ΦC Φv`. Then its defined adelic Fourier transform is
exactly the indicator of `integralOutside F n S` times the product of:

- `ArchimedeanLocal.realFourierTransform (aR v) (ΦR v)` at the real row coordinates;
- `ArchimedeanLocal.complexFourierTransform (aC w) (ΦC w)` at the complex row coordinates;
- `padicRowFourier (padicField v) (ψv v) (νv v) n (Φv v)` at each finite row coordinate for `v ∈ S`.

The constant in this function equality is exactly one. The global measure is the
published `rectangleMeasure F 1 n`. The real and complex measures are the
published `realSelfDualMeasure` and `complexSelfDualMeasure` associated with the
supplied scales. The Fourier character has the plus sign everywhere.

`padicRowFourier` is only a wrapper for the existing
`Langlands.HarmonicAnalysis.rowFourierIntegral`: it installs the p-adic field's
canonical topology and its Borel measurable space and then uses the finite
product of `νv.measure`. It does not choose a normalization or an independent
Fourier transform. Its integrand is the local character of the row pairing times
the local function, in the order used by `rowFourierIntegral`.

No locally constant or compact support assumption is needed on `Φv` for this
conditional equality of totalized integrals. For membership of the assembled
function in the Schwartz–Bruhat space, the separately published
`restrictedTensor_mem_schwartzBruhat` still requires those assumptions at `S`.
The result asserts no additional convergence theorem. Empty sets of real,
complex or finite places and `n = 0` are included. In particular the formula
specializes to `n = r + 1` with `r = 0` in the equal-rank target.

## Implemented proof

`finite_character_product` subtracts the finite partial sum supported on `S`
from an adele with zero infinite component and finite part integral outside `S`.
The residual has zero coordinates in `S` and integral coordinates outside `S`.
The published `character_eq_one_of_integralOutside` therefore makes its character
one. Additivity and the supplied canonical component equalities give precisely
the product over `S`. This argument uses no enlargement by an auxiliary character
control set.

`infinite_character_product` uses the published decomposition into infinite
components, separates the real and complex places, and applies the supplied
component equalities. `pairing_character_product` combines the finite and
infinite formulas for the adele `∑ j, x 0 j * y 0 j`. When both rows are integral
outside `S`, each finite component of this sum is integral outside `S`, by closure
of the valuation subring under products and finite sums. Explicit ring
homomorphisms show that every coordinate of the pairing is the local row pairing.
The Circle character products are then coerced to complex numbers.

`integral_row_matrix` uses Mathlib's `measurePreserving_piUnique` to integrate
out the unique row index. Consequently `rectangular_fourier_integral` identifies
the one-row rectangular integral with the generic local Fourier integral.
`padicRect_fourier_integral` makes the same identification in the canonical
p-adic measurable spaces and commutes the two complex factors in the integrand.
`rectIntegralOutside_row` and the three coordinate lemmas identify the one-row
rectangular domain and projections with their row counterparts.

For an output row inside `integralOutside`, the main proof multiplies each local
function by its local pairing character. The restricted tensor's product formula
and `pairing_character_product` make the global Fourier integrand exactly the
indicator times this product of local functions. The assumed
`RectangleTateStatement` is applied with one row and `n` columns. The one-row
integral identifications yield the specified real, complex and finite local
Fourier transforms, without a scalar correction.

For an output row outside `integralOutside`, the previously published
`fourierStandardOutside` theorem gives vanishing, since the assembled tensor is
standard outside `S`. This agrees with the indicator in the claimed formula.

## Remaining obligations

`RectangleTateStatement` remains an explicit open premise. To use the finite
factors with equal-rank local test data, their recorded `IsRowFourierPair`
relations identify each `padicRowFourier` value with its prescribed Fourier
partner. The representation-theoretic realization of the global and local
Whittaker functions, the quotient measure comparison, and the nonvanishing
claims required by `ArchimedeanFactorizationStatement` are not supplied here.
The unconditional proof required by Task 7397 remains open.
