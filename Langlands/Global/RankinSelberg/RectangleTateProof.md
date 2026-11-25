# Proof: Tate's factorization of the rectangular measure (premise C)

The theorem `Langlands.Global.RankinSelbergGlobal.RectangleTate.rectangleTateStatement`
proves `Langlands.Global.RankinSelbergGlobal.RectangleTateStatement.{u}`: premise C of the
Library's reduction `ArchimedeanFactorizationReduction` (towards `ArchimedeanFactorizationStatement`). Its only axioms are
`propext`, `Classical.choice` and `Quot.sound`.

**Statement (recalled).** Let `F` be a number field with `𝔸 / F` compact, and `ψ` a unitary
character of `𝔸` trivial on `F`. Suppose `ψ` has conductor zero at every finite place outside
`S` (`FiniteAdditiveSupport ψ S`). Let its components be `x ↦ e(a_v x)` at the real places,
`z ↦ e(Tr(a_w z))` at the complex places and `ψv v` at the finite places. Let `νv v` be
self-dual for `ψv v`. Then for all functions `hR v`, `hC w`, `hS v` on the local matrix spaces
`M_(k,m)`, the integral against `rectangleMeasure F k m` of the product
`∏_v hR v(x_v) ∏_w hC w(x_w) ∏_(v ∈ S) hS v(x_v)`, cut off by integrality of `x` outside `S`,
is the product of the local integrals for the measures `realSelfDualMeasure (aR v)`,
`complexSelfDualMeasure (aC w)` and `νv v`, with constant one.

Mathematically this is Tate's theorem that the self-dual measure of `𝔸` gives `𝔸 / F` volume
one (Tate's thesis, §4, in Cassels–Fröhlich 1967). Together with uniqueness of Haar measure,
it identifies the covolume-one measure with the product of the self-dual local measures.
The Lean proof reaches this through the Library's Hecke development. The modules
`RectangleTateMeasure` and `RectangleTateCore` (see their Markdown) supply the measure
theory. This module supplies the archimedean volume, the transfer of the `p`-adic integrals
between topologies and the assembly.

## `archVolume`

For `aR : real places → ℝˣ` and `aC : complex places → ℂˣ`,

```text
((pi_v realSelfDualMeasure (aR v)).prod (pi_w complexSelfDualMeasure (aC w))) (archDomain F)
  = ofReal (mixedGaussianConst aR aC · covol(idealLattice F (integerIdeal F))).
```

Proof. `realSelfDualMeasure a` is `√‖a‖₊ • volume`. `complexSelfDualMeasure a` is
`‖a‖₊ • (2 • volume)`, which is `(‖a‖₊ · 2) • volume`. By `pi_smul_eq`,
`Measure.prod_smul_left` and `Measure.prod_smul_right`, the product measure is
`(∏_v √‖aR v‖₊ · ∏_w ‖aC w‖₊ · 2) • volume` on the mixed space. The scalar is
`ofReal (mixedGaussianConst aR aC)`, where `mixedGaussianConst aR aC = ∏ √|aR v| · ∏ 2‖aC w‖`
(`ENNReal.ofReal_prod_of_nonneg`, `Real.coe_sqrt`). The volume of the parallelepiped
`archDomain F` is the covolume of the lattice
(`ZLattice.covolume_eq_measure_fundamentalDomain`, `fundamentalDomain_idealLattice`, finiteness
from `ZSpan.fundamentalDomain_isBounded`).

## `padicRectIntegral_haarMeasureCongr`

Let `t` be a topology on `F_v` equal to the canonical topology of `padicField v`, and `μ` a Haar
measure for `t`. Then `padicRectIntegral (padicField v) k m (haarMeasureCongr ht μ) f` is the
integral of `f` against `pi_i pi_j μ` for the Borel structure of `t`. Proof: `subst` the
equality of topologies; both sides are then the same term.

## The main theorem

Introduce all binders of the statement. Then:

1. **Finite components in the completion topology.** `ψf v = ofCanonicalCharacter v (ψv v)` is
   `ψv v` read in the topology of `topologicalData v`. It is a finite component of `ψ`
   (`IsFiniteAdditiveComponent`): this is the hypothesis on `ψv v` unfolded. Let
   `μ v = Classical.choice (nonempty_selfDualHaar v (ψf v))`, a self-dual Haar measure for
   `topologicalData v`, and `ν v = (μ v).val.measure` for `v ∈ S`.
2. **Conductors.** For `v ∉ S`, `FiniteAdditiveSupport ψ S` gives a canonical component `ψz` of
   conductor `0`. It has the same values as `ψv v`, since both are restrictions of `ψ`. So
   `additiveConductor_congr` with `topologicalData_eq_canonicalTopologicalData` gives conductor
   `0` for `ψf v`. Hence the conductors form a finitely supported vector `n`
   (`Finsupp.onFinset S`) with support in `S`.
3. **Tamagawa normalization.** The Library's
   `Hecke.mixedGaussianConst_mul_covolume_mul_prod_latticeMass` takes the product formula
   `additiveProductFormula_of_global ψ hdiag ψf hf aR haR aC haC`, the vector `n`, the measures
   `μ`, `m = 0` and the set `S`. It gives
   `mixedGaussianConst aR aC · covol(idealLattice F (latticeIdeal 0)) · ∏_(v ∈ S) latticeMass_v(0) = 1`.
   Here `latticeMass_v(0) = (μ v)(L_v(0)).toReal`, and `L_v(0) = 𝒪_v` by
   `Hecke.mem_additiveLattice_zero_iff`, so `latticeMass_v(0) = (ν v (𝒪_v)).toReal`. This mass
   is finite because `𝒪_v` is compact.
4. **Normalization hypothesis.** By `archVolume` and step 3,
   `λ(archDomain F) · ∏_(v ∈ S) ν v (𝒪_v) = ofReal(1) = 1`. Here λ is the product of the
   archimedean self-dual measures (`ENNReal.ofReal_mul`, `ENNReal.ofReal_prod_of_nonneg`,
   `Finset.prod_coe_sort`).
5. **Assembly.** `RectangleTate.integral_indicator_rect` with the archimedean self-dual
   measures and `ν` rewrites the left side of the statement as `scalar · (product of local
   integrals)`. By `RectangleTate.scalar_eq_one` and step 4, `scalar = 1`. The real and complex
   local integrals are the statement's integrals over `rectangularMeasure`, definitionally.
   At `v ∈ S`, `νv v` and `haarMeasureCongr _ (μ v).val` are both self-dual for `ψv v`: the
   first by hypothesis, the second by `isSelfDualMeasure_haarMeasureCongr`. So both are equal
   to `localSelfDualHaar (ψv v)` (`Correspondence.eq_localSelfDualHaar`).
   `padicRectIntegral_haarMeasureCongr` then turns `padicRectIntegral (padicField v) k m (νv v) (hS v)`
   into `∫ hS v d(pi_i pi_j ν v)`.

No integrability hypothesis on `hR`, `hC`, `hS` is needed. All the product formulas used
(`integral_prod_mul`, `integral_fintype_prod_eq_prod`) hold for arbitrary functions.
