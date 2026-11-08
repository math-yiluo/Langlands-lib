# Lattices of a number field with prescribed local components

Module `Langlands.Global.Hecke.AdelicLattice`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `FinitePlace K` its finite places (height-one primes of
`𝓞 K`), `K_v = FiniteCompletion K v` the completion, and `topologicalData v =
CompletionPadic.topologicalData v` the local-field data of `K_v` used by the published local
Tate theory. For an integer `k`, `L_v(k) = (topologicalData v).additiveLattice k` is the
valuation lattice `π_v^{-k} O_v` (elements of discrete valuation `≤ exp k`), and
`n_v = (topologicalData v).additiveConductor ψ_v` is the additive conductor of a nontrivial
unitary additive character `ψ_v` of `K_v`, the largest `n` with `ψ_v` trivial on `L_v(n)`.
`V = mixedSpace K = ℝ^{real places} × ℂ^{complex places}` is the mixed space with Lebesgue
measure, `ι = mixedEmbedding K : K → V`, and `idealLattice K I = ι(I) ⊆ V` is the lattice of a
fractional ideal `I`. For real scales `aR` at the real places and complex scales `aC` at the
complex places, `T = addTrace aR aC` is the linear form
`T(x) = Σ aR_v x_v + Σ 2 Re(aC_v x_v)`, `B = tracePairing aR aC` is the bilinear form
`B(x, y) = -T(x y)`, and `κ = mixedGaussianConst aR aC = ∏ √|aR_v| ∏ 2 ‖aC_v‖`; these are
defined in `Langlands.Global.Hecke.MixedSpaceFourier`. `𝐞 x = exp(2πix)` is Mathlib's
`Real.fourierChar`.

The module collects the arithmetic of global lattices cut out by local conditions, which the
proof of the Hecke global functional equation needs in order to do Poisson summation over `K`
with test functions that are tensors of archimedean and `p`-adic pieces: membership through
local valuations, norms, strong approximation, local masses of valuation lattices under
self-dual Haar measures, the trace-dual of an ideal lattice for a character satisfying the
additive product formula, finiteness of the conductor support, and the Tamagawa normalization.
It is an internal helper module and states nothing about `L`-functions.

## Provenance

Internal helper for the proof of the published actual Hecke global functional equation
statement. The mathematics is the additive theory of §4.1 of Tate's thesis (J. T. Tate,
*Fourier analysis in number fields and Hecke's zeta-functions*, in Cassels–Fröhlich,
*Algebraic Number Theory* (1967), pp. 305–347), transported from adeles to lattices in the
mixed space:

- `dualSubmodule_idealLattice` is the lattice form of Tate's Theorem 4.1.4 (p. 331,
  `k^* = k`: the adele classes orthogonal to `K` under the global character are exactly `K`).
  Tate's proof uses the duality theory of the compact group `V mod k`; here the inclusion
  `Λ_{n-m} ⊆ Λ_m^*` comes from the product formula (the analogue of Tate's Lemma 4.1.5,
  p. 331), and the reverse inclusion from strong approximation: the dual lattice contains an
  ideal lattice of finite index, so its vectors come from `K`, and a non-integrality at a
  single place is detected by an element of `Λ_m` built by strong approximation.
- `mixedGaussianConst_mul_covolume_mul_prod_latticeMass` is the lattice form of Tate's
  Theorem 4.1.3 (2) (pp. 330–331: the additive fundamental domain has measure `1` for the
  self-dual measure), proved here not by Tate's discriminant computation but by the argument of
  Tate's remark closing §4.2 (pp. 333–334: a self-dual measure gives the quotient a measure
  whose square is `1`), applied to the pair `Λ_0`, `Λ_n = Λ_0^*`.
- `finite_setOf_additiveConductor_ne_zero` has no counterpart in Tate, who works with a fixed
  standard character whose local conductors are the exponents of the different. It replaces
  that explicit description for an arbitrary family of local characters satisfying the
  product formula.
- `exists_approx` is the strong approximation theorem in the form "finitely many congruence
  conditions and integrality elsewhere", derived from the published
  `exists_sub_mem_integralFiniteAdeles` (`K + Ô` is all of the finite adeles).
- The local mass `μ(O_v) = q_v^{-n_v/2}` of a self-dual Haar measure is extracted from the
  published local normalization theorem `LocalFactors.padicFourierNormalization`.

The shape of all statements (finitely supported level vectors, the hypothesis
`AdditiveProductFormula`, a finite set `S₀` outside which conductors are nonnegative) is
chosen for the internal assembly and is not taken from the literature.

## Definitions

- `latticeIdeal m : (FractionalIdeal (𝓞 K)⁰ K)ˣ` for a finitely supported level vector
  `m : FinitePlace K →₀ ℤ` is the fractional ideal `∏ 𝔭_v^{-m v}`, defined as
  `ClassField.Global.finiteDivisorFractionalIdeal K (-m)`.
- `latticeMass T ψ μ k : ℝ`, for local-field data `T` of a `p`-adic field, an additive
  character `ψ`, a self-dual Haar measure `μ : SelfDualHaar T ψ` and `k : ℤ`, is the real mass
  `(μ (L(k))).toReal` of the valuation lattice `L(k) = T.additiveLattice k`.
- `AdditiveProductFormula aR aC ψf : Prop`, for archimedean scales and a family
  `ψf v` of unitary additive characters of the completions `K_v`, says: for every `x ∈ K` there
  is a finite set `S` of finite places with `ψf v x = 1` for `v ∉ S` and
  `𝐞(T(ι x)) · ∏_{v ∈ S} ψf v x = 1`. (The global additive character `𝐞 ∘ T × ∏ ψ_v` is
  trivial on `K`.)

## Main results

### Valuations of global elements

- `mem_additiveLattice_iff_valued`: `x ∈ L_v(k) ↔ Valued.v x ≤ exp k` for `x ∈ K_v`.
- `discreteValuation_algebraMap`: the discrete valuation of `topologicalData v` on the image of
  `γ ∈ K` is the `v`-adic valuation `v.valuation K γ`.
- `algebraMap_mem_additiveLattice_iff`: `γ ∈ L_v(k) ↔ v.valuation K γ ≤ exp k` for `γ ∈ K`.
- `mem_additiveLattice_zero_iff`: `L_v(0)` is the ring of integers `adicCompletionIntegers`.
- `finite_setOf_not_mem_additiveLattice_zero γ`: `γ ∈ K` lies in `L_v(0)` for all but
  finitely many `v`.

### Fractional ideals with prescribed local lattices

- `valuation_eq_exp_neg_count`: for `a ≠ 0`, `v.valuation K a = exp(-count_v (a))`, where
  `count_v` is the multiplicity of `v` in the principal fractional ideal `(a)`.
- `le_of_forall_count_le`: for nonzero fractional ideals, if `count_v I ≤ count_v J` for all
  `v`, then `J ≤ I`.
- `count_latticeIdeal`: `count_v (latticeIdeal m) = -m v`.
- `mem_latticeIdeal_iff`: `γ ∈ latticeIdeal m ↔ ∀ v, v.valuation K γ ≤ exp (m v)`.
- `mem_latticeIdeal_iff_forall_mem`: `γ ∈ latticeIdeal m ↔ ∀ v, γ ∈ L_v(m v)`.
- `absNorm_latticeIdeal`: `N(latticeIdeal m) = ∏_{v ∈ supp m} N(𝔭_v)^{-m v}` (in `ℚ`).

### Strong approximation

- `exists_approx S c m`: for a finite set `S` of finite places, centres `c v ∈ K_v` and
  integers `m v`, there is `x ∈ K` with `x - c v ∈ L_v(m v)` for `v ∈ S` and `x ∈ L_v(0)` for
  `v ∉ S`.

### Self-dual Haar measures of valuation lattices

Here `T` is local-field data of a `p`-adic field with residue cardinality `q`, `ψ` a unitary
additive character with conductor `n = T.additiveConductor ψ`, `μ : SelfDualHaar T ψ` and the
Borel σ-algebra is used.

- `selfDualHaar_integerRing`: `μ(O) = q^{-n/2}`.
- `selfDualHaar_additiveLattice`: `μ(L(m)).toReal = q^m q^{-n/2}`.
- `latticeMass_eq`: `latticeMass T ψ μ k = q^k q^{-n/2}`.
- `measure_additiveLattice_mul_measure_dual`, `latticeMass_mul_dual`:
  `μ(L(m)) μ(L(n - m)) = 1`.

### Lattices in the mixed space

- `covolume_eq_of_span_eq`: if a real basis `b` of `V` spans the lattice `L` over `ℤ`, then
  `covol(L) = vol(parallelepiped b)`.
- `exists_nsmul_mem_of_le`: if `L₁ ≤ L₂` are full lattices of `V`, there is `k ≠ 0` in `ℕ` with
  `k w ∈ L₁` for every `w ∈ L₂`.

### The trace-dual of an ideal lattice

`Λ^*` denotes `(tracePairing aR aC).flip.dualSubmodule Λ = {w | ∀ y ∈ Λ, B(y, w) ∈ ℤ}`, and
`Λ_m = idealLattice K (latticeIdeal m)`.

- `fourierChar_eq_one_iff`: `𝐞 x = 1 ↔ x ∈ ℤ`.
- `mul_mem_additiveLattice`: `L_v(a) L_v(b) ⊆ L_v(a + b)`.
- `addTrace_mem_of_forall_mem`: under `AdditiveProductFormula`, if `x ∈ K` lies in `L_v(n_v)`
  for every `v`, then `T(ι x) ∈ ℤ`.
- `mem_dualSubmodule_of_forall_mem`: under `AdditiveProductFormula`, if `μ ∈ L_v(k_v)` for every
  `v` and `m_v + k_v ≤ n_v`, then `ι μ ∈ Λ_m^*`.
- `idealLattice_le_dualSubmodule`: under `AdditiveProductFormula`, if `m_v + m'_v ≤ n_v` for
  every `v`, then `Λ_{m'} ⊆ Λ_m^*`.
- `dualSubmodule_idealLattice_eq_span`: if all `aR v, aC v` are nonzero, `(ι I)^*` is the
  `ℤ`-span of the `B`-dual basis of the lattice basis `fractionalIdealLatticeBasis K I`.
- `exists_eq_of_mem_dualSubmodule`: if all scales are nonzero and `Λ_{m'} ⊆ Λ_m^*`, every
  vector of `Λ_m^*` is `ι μ` for some `μ ∈ K`.
- `mem_additiveLattice_of_mem_dualSubmodule`: under `AdditiveProductFormula`, if `n_v ≥ 0` for
  `v ∉ S₀` (a finite set) and `ι μ ∈ Λ_m^*`, then `μ ∈ L_v(n_v - m_v)` for every `v`.
- `finite_setOf_additiveConductor_ne_zero`: if all scales are nonzero, the product formula
  holds and `n_v ≥ 0` for `v ∉ S₀`, then `{v | n_v ≠ 0}` is finite.
- `dualSubmodule_idealLattice`: if all scales are nonzero, the product formula holds and
  `n_v = n v` for a finitely supported `n`, then `Λ_m^* = Λ_{n - m}` for every finitely
  supported `m`.

### Tamagawa normalization

- `mixedGaussianConst_mul_covolume_mul_prod_latticeMass`: if all scales are nonzero, the
  product formula holds, `n_v = n v` for a finitely supported `n`, `μ_v` are self-dual Haar
  measures for `ψ_v`, and the finite set `S` contains the supports of `m` and `n`, then

  `κ · covol(Λ_m) · ∏_{v ∈ S} latticeMass (topologicalData v) (ψf v) (μ v) (m v) = 1`.

## Proofs

**Valuations.** `topologicalData v` is the local-field data of the completion produced by
`AdelicFunctoriality.FiniteExtension`, whose discrete valuation is the completion valuation
(`topologicalData_discreteValuation`); on elements of `K` this is `v.valuation K`
(`valuedAdicCompletion_eq_valuation'`). Finiteness of non-integral places is
`HeightOneSpectrum.Support.finite`.

**Lattice ideals.** `valuation_eq_exp_neg_count` writes `a = n/d` with `n, d ∈ 𝓞 K`, computes
`count_v (a) = count_v (n) - count_v (d)` by `FractionalIdeal.count_well_defined`, and compares
with `valuation_of_mk'` and `intValuation`. For `le_of_forall_count_le`, the factorization
`J I⁻¹ = ∏ 𝔭_w^{count_w(J I⁻¹)}` has only nonnegative exponents, so `J I⁻¹ ≤ 1` and
`J ≤ I`. Then `mem_latticeIdeal_iff` reduces `γ ∈ latticeIdeal m` to
`(γ) ≤ latticeIdeal m`, which by `count_mono` and `le_of_forall_count_le` is equivalent to
`count_v (γ) ≥ -m v` for all `v`, i.e. `v.valuation K γ ≤ exp (m v)`. The norm formula is
multiplicativity of `FractionalIdeal.absNorm` on the published product formula
`finiteDivisorFractionalIdeal_val`.

**Strong approximation.** Let `δ = (∏_{v ∈ S} N 𝔭_v)^k ∈ 𝓞 K` with `k = Σ_{v∈S} |m v|`, so
`v(δ) ≤ exp(-k) ≤ exp(m v)` for `v ∈ S`. Apply `exists_sub_mem_integralFiniteAdeles` to the
finite adele `a` with `a_v = δ⁻¹ c_v` for `v ∈ S` and `a_v = 0` otherwise: there is `x' ∈ K`
with `a - x'` integral. Then `x = δ x'` works: for `v ∈ S`,
`x - c_v = -δ (δ⁻¹ c_v - x')` has valuation `≤ v(δ) ≤ exp (m v)`, and for `v ∉ S`,
`x = δ x'` is a product of integers.

**Local masses.** The published normalization theorem `padicFourierNormalization` states that
a Haar measure is self-dual for `ψ` exactly when it gives the integers the mass `q^{-n/2}`; the
self-duality of `μ` (Fourier inversion with `f(-x)`) is converted to the form used there.
`padicLatticeHaar` gives `μ(L(m)) = q^m μ(O)`. The product formula
`μ(L(m)) μ(L(n - m)) = q^m q^{n-m} q^{-n} = 1` is an `rpow` computation.

**Covolumes.** `covolume_eq_of_span_eq` is `ZLattice.covolume_eq_measure_fundamentalDomain`
with the fundamental domain of `ZSpan`, which is a.e. the parallelepiped. For
`exists_nsmul_mem_of_le`, transport both lattices to Euclidean space by
`mixedEmbedding.euclidean.toMixed`; the covolume ratio formula
`ZLattice.covolume_div_covolume_eq_relIndex'` shows that the relative index `r` is nonzero
(the covolumes are positive), and `AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd` gives
`r! w ∈ L₁` for `w ∈ L₂`.

**Easy dual inclusion.** If `l ∈ latticeIdeal m` and `μ ∈ L_v(k_v)` with `m_v + k_v ≤ n_v`,
then `l μ ∈ L_v(n_v)` at every place, so `ψ_v(l μ) = 1` everywhere (`additiveConductor_spec`),
and the product formula gives `𝐞(T(ι(l μ))) = 1`, i.e. `T(ι l · ι μ) ∈ ℤ`, i.e.
`B(ι l, ι μ) ∈ ℤ`.

**Dual vectors come from `K`.** By `dualSubmodule_idealLattice_eq_span` and
`LinearMap.BilinForm.dualSubmodule_span_of_basis`, `Λ_m^*` is a full lattice, and
`exists_nsmul_mem_of_le` applied to `Λ_{m'} ⊆ Λ_m^*` gives `k ≠ 0` with `k w = ι β`,
`β ∈ latticeIdeal m'`, for every `w ∈ Λ_m^*`; then `w = ι(β/k)`.

**Hard dual inclusion (local form).** Suppose `ι μ ∈ Λ_m^*` but `μ ∉ L_{v₀}(n_{v₀} - m_{v₀})`.
Then `μ ≠ 0` and, by `forall_mul_eq_one_iff_mem_additiveLattice`, some `t ∈ L_{v₀}(m_{v₀})`
has `ψ_{v₀}(t μ) ≠ 1`. Let `e_v` be the valuation exponent of `μ` at `v` and let `S` consist
of `v₀`, `S₀`, the support of `m` and the places where `μ` is not integral. Strong
approximation gives `l ∈ K` with `l - t ∈ L_{v₀}(min(m_{v₀}, n_{v₀} - e_{v₀}))`,
`l ∈ L_v(min(m_v, n_v - e_v))` for `v ∈ S \ {v₀}` and `l` integral outside `S`. Then
`l ∈ latticeIdeal m`, `ψ_v(l μ) = 1` for every `v ≠ v₀` (`l μ ∈ L_v(n_v)` inside `S`; outside
`S`, `l μ` is integral and `n_v ≥ 0`), and `ψ_{v₀}(l μ) = ψ_{v₀}(t μ)` since
`(l - t) μ ∈ L_{v₀}(n_{v₀})`. As `ι l ∈ Λ_m`, `T(ι(l μ))` is an integer, so the product
formula forces `ψ_{v₀}(t μ) = 1`, a contradiction.

**Finiteness of the conductor support.** Put `m'' = min(n, 0)` on `S₀` and `0` elsewhere;
`0 + m''_v ≤ n_v` everywhere, so `Λ_{m''} ⊆ Λ_0^*`, and every vector `b'_j` of the `B`-dual basis
of `Λ_0` is `ι μ_j` with `μ_j ∈ K`. Let `v` be a place outside `S₀` where all `μ_j` are
integral, and suppose `n_v ≠ 0`, so `n_v ≥ 1`. Strong approximation on `{v} ∪ S₀` gives `l ∈ K`
with `l - π_v^{-1}` integral at `v`, `l ∈ L_w(min(n_w, 0))` for `w ∈ S₀` and `l` integral
elsewhere; then `l ∈ L_w(n_w)` at every place (at `v` because `π_v^{-1} ∈ L_v(1) ⊆ L_v(n_v)`).
By the easy inclusion, `ι l ∈ Λ_0^* = span_ℤ (b'_j)`, so `l = Σ c_j μ_j` is integral at `v`, and
then `π_v^{-1} = l - (l - π_v^{-1})` is integral at `v`, contradicting
`inverse_uniformizer_not_mem_integers`. Hence `{n_v ≠ 0}` lies in the finite set
`S₀ ∪ ⋃_j {v | μ_j not integral at v}`.

**The trace-dual.** `Λ_{n-m} ⊆ Λ_m^*` is the easy inclusion. Conversely, a vector of `Λ_m^*` is
`ι μ` with `μ ∈ K`, and the local form of the hard inclusion (with `S₀ = supp n`) gives
`μ ∈ L_v(n_v - m_v)` for all `v`, i.e. `μ ∈ latticeIdeal (n - m)`.

**Tamagawa normalization.** By `mixedEmbedding.covolume_idealLattice`,
`covol(Λ_{m'}) = N(latticeIdeal m') covol(Λ_0) = ∏_{v ∈ supp m'} q_v^{-m'_v} covol(Λ_0)`
(`absNorm_latticeIdeal`, `residueCardinality_eq`), and `latticeMass (m'_v) = q_v^{m'_v}
q_v^{-n_v/2}`. Hence for every `m'` supported in `S` the product
`κ covol(Λ_{m'}) ∏_{v ∈ S} latticeMass(m'_v)` equals the constant
`X = κ covol(Λ_0) ∏_{v∈S} q_v^{-n_v/2}`. With `b` the lattice basis of `Λ_0` and `b'` its
`B`-dual basis, `covol(Λ_0) = vol(b)` and `covol(Λ_n) = vol(b')` (`Λ_n = Λ_0^*` by
`dualSubmodule_idealLattice`). Evaluating `X` at `m' = 0` and at `m' = n` and multiplying,
`X² = vol(b) vol(b') κ² ∏_{v ∈ S} latticeMass(0) latticeMass(n_v) = 1` by
`measureReal_parallelepiped_mul_dualBasis` (from `MixedSpaceFourier`) and
`latticeMass_mul_dual`. Since `X ≥ 0`, `X = 1`.
