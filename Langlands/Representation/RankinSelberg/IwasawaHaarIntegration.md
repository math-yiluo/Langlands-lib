# Iwasawa integration on the whole group `GL_(n+1)`

Module `Langlands.Representation.RankinSelberg.IwasawaHaarIntegration`,
namespace `Langlands.RankinSelberg.IwasawaHaar`.

Write `m = n + 1`, `G = GeneralLinear m E`, `N = upperUnipotent m E`,
`A = Fin m → Eˣ` and
`K = Conductor.integralSubgroup (ValuativeRel.valuation E).integer n`.
The measures are the Library's normalized ones:
`du = unipotentHaar E n` (mass one on the integral unipotent subgroup),
`da = Measure.pi (fun _ => localMultiplicativeHaar E)` (mass one on each
integral-unit factor), `dg = generalLinearHaar E n` (mass one on `K`) and
`dk = dg.restrict K`.

The main result, in the normalizations of the published
`QuotientIwasawaIntegrationStatement`, is

```text
dg = Measure.map (fun (u, a, k) => u * diag(a) * k)
       ((du × (da × dk)).withDensity (fun (u, a, k) => ENNReal.ofReal (δ(a)⁻¹))),
δ(a) = ∏_{i<j} T.normalizedAbs(a_i / a_j).
```

It is the whole-group counterpart of the quotient formula
`QuotientIwasawaIntegrationStatement`, whose paired Markdown relates it to
JPSS Theorem 2.7 (printed p391, equation (3)). The whole-group form and all
statements in this module are internal derived content. Apart from the two
Bochner-integral forms, which assume the integrand is integrable on `G`, they
state no integrability or convergence hypothesis: they are identities of
measures or of nonnegative extended integrals for measurable functions.

## Algebra (section `Algebra`, any field `E`)

- `borelPoint x = diag(x.1) * x.2`: Borel coordinates `(a, u) ↦ diag(a) u`.
- `shiftUnipotent x₀ a = diagonalConj (x₀.1⁻¹ * a)⁻¹ x₀.2⁻¹` and
  `borelShift x₀ x = (x₀.1⁻¹ * x.1, shiftUnipotent x₀ x.1 * x.2)`.
- `borelPoint_shift`: `borelPoint (borelShift x₀ x) = (borelPoint x₀)⁻¹ * borelPoint x`.
  So left translation by an element of the Borel subgroup is a map of Borel coordinates.
- `exists_borelPoint_mul` (nonarchimedean local field): every `y ∈ G` is
  `borelPoint x₀ * k₀` with `k₀ ∈ K`. This follows from the Library's algebraic
  Iwasawa decomposition `Iwasawa.exists_iwasawa`, after commuting the torus
  factor past the unipotent factor with `diagonalConj`.
- `borelPoint_mem_iff`: `diag(a) u ∈ K` exactly when every `a i` is an
  integral unit and `u ∈ K`. The forward direction reads the diagonal entries of
  an integral upper triangular matrix (`Iwasawa.valuation_diag_eq_one`).

## General measure statements (section `Measure`)

Here `E` is a nonarchimedean local field that is Hausdorff and second countable,
and `Eˣ`, `G` and `N` carry Borel σ-algebras. The private instances supply local
compactness and second countability of the matrix space, `G`, `N` and `Eˣ`.
In every statement, `w : A → ℝ≥0∞` is a density for diagonal conjugation on `N`:

```text
hw : ∀ a, (unipotentHaar E n).map (diagonalConj a) = w a • unipotentHaar E n.
```

- `continuous_borelPoint`, `continuous_diagonalConj_prod` (joint continuity of
  `(a, u) ↦ diag(a) u diag(a)⁻¹`), `continuous_borelShift_snd`,
  `continuous_iwasawaPoint`: continuity facts.
- `measurePreserving_borelShift`: `borelShift x₀` preserves `da × du`.
- `measure_borelPoint_preimage`: `(da × du)(borelPoint⁻¹' K) = 1`.
- `measurable_of_map_diagonalConj`: any such `w` is measurable.
- `lintegral_borelPoint`: for measurable `h : G → ℝ≥0∞`,
  `∫ h(diag(a) u) d(da × du) = ∫_A w(a) ∫_N h(u diag(a)) du da`.
- `lintegral_generalLinearHaar` (iterated form): for measurable `f : G → ℝ≥0∞`,
  `∫_G f dg = ∫_K ∫_A w(a) ∫_N f(u diag(a) k) du da dk`.
- `iwasawaPoint (u, a, k) = u * diag(a) * k`.
- `lintegral_generalLinearHaar_prod` (product form):
  `∫_G f dg = ∫ w(a) f(u diag(a) k) d(du × (da × dk))`.
- `generalLinearHaar_eq_map` (measure form):
  `dg = Measure.map iwasawaPoint ((du × (da × dk)).withDensity (fun x => w x.2.1))`.
- `integral_generalLinearHaar` (Bochner form): if moreover `w a ≠ ⊤` for every
  `a`, then for every `f : G → ℂ` integrable for `dg`,
  `∫_G f dg = ∫_K ∫_A (w a).toReal * ∫_N f(u diag(a) k) du da dk`,
  with the unipotent integral innermost.

## The `p`-adic statement (section `Padic`)

`generalLinearHaar_eq_map_iwasawa (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ)`
proves the displayed identity. It uses the same `letI` setup as
`QuotientIwasawaIntegrationStatement`: the topology, valuation and local-field
structure from `T`, and Borel σ-algebras on `F.Carrierˣ`, `G` and `N`. It also uses
the same `A`, `da`, `K`, `dk` and `δ`. The pushforward map is written
`fun x => x.1.val * Iwasawa.diagonalUnits x.2.1 * x.2.2`. It needs no
right-invariance hypothesis on `du`.

`integral_generalLinearHaar_iwasawa F T n`, in the same setup, is the Bochner form:
for every `f : G → ℂ` integrable for `dg`,

```text
∫_G f dg = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk,
```

where `δ(a)⁻¹` is the real number `(δ a)⁻¹` cast to `ℂ`.

## Proof

The factorization theorem `CompactFactorization.lintegral_restrict_lintegral_mul`
from the Library is applied with parameter space `X = A × N`, parameter measure
`ρ = da × du`, coordinate map `ι = borelPoint` and compact subgroup `K`. Its
hypotheses are met as follows:

- `G = ι(X) K` by `exists_borelPoint_mul`;
- for each `x₀`, the map `borelShift x₀` preserves `ρ`. This is
  `measurePreserving_borelShift`: left multiplication on `A` is a skew product
  with a fiberwise left translation of `N`, so it preserves `ρ` by
  `MeasurePreserving.skew_product`. It also satisfies
  `ι(borelShift x₀ x) = ι(x₀)⁻¹ ι(x)` by `borelPoint_shift`.

The theorem gives `∫_K ∫_X f(ι(x) k) dρ dk = ρ(ι⁻¹ K) ∫_G f dg`. Here
`ρ(ι⁻¹ K) = 1` by `borelPoint_mem_iff`: the preimage is the product of the integral
unit groups and the integral unipotent subgroup, all of mass one. Then
`lintegral_borelPoint` rewrites the inner integral. By Tonelli on `A × N` it is
an iterated integral. In the fiber over `a`, write
`diag(a) u = (diag(a) u diag(a)⁻¹) diag(a)` and change variables along
`diagonalConj a`, which contributes the factor `w(a)` from `hw`. This is the
iterated form. The product form follows by Tonelli (`lintegral_prod_symm` twice), using the
measurability of `w` from `measurable_of_map_diagonalConj`. That lemma writes
`w(a)` as the `du`-mass of the `a`-section of a measurable set, then applies
`measurable_measure_prodMk_left`. The measure form evaluates the product form on
indicator functions.

The Bochner form rewrites `dg` by the measure form. `integral_map` and
`integral_withDensity_eq_integral_toReal_smul` (which needs `w < ⊤`) turn
`∫_G f dg` into the integral of `(w a).toReal • f(u diag(a) k)` over
`du × (da × dk)`. That integrand is integrable by
`integrable_map_measure` and `integrable_withDensity_iff_integrable_smul'`.
Fubini (`integral_prod_symm`, twice) then gives the iterated integral, and the
real scalar is pulled out of the unipotent integral.

For the `p`-adic statement, `T.fieldT2` and `T.secondCountableTopology` supply
the topological hypotheses, and the density is `w(a) = ENNReal.ofReal (δ(a)⁻¹)`.
The published `diagonalConj_map` gives `hw` with the scalar equal to the inverse
singleton-block Levi modulus, and `singleton_modulus_real` identifies that modulus
with `δ(a)`. The `p`-adic Bochner form applies `integral_generalLinearHaar` to
the same density; `ENNReal.ofReal (δ(a)⁻¹)` is finite and its real part is
`δ(a)⁻¹` because `δ(a) ≥ 0`.

The route differs from the quotient proof `quotientIwasawaIntegration`. It uses
neither the quotient, nor compatibility of quotient measures, nor the torus-sum
decomposition. It needs only the group factorization, the measure-preserving
Borel shifts and the diagonal-conjugation scaling.
