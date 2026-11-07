# Poisson summation for lattices in finite-dimensional real spaces

Module `Langlands.Global.Hecke.LatticePoissonGeneral`, namespace `Langlands.Global.Hecke`.

This module transports Poisson summation on `ℤ^ι` (module
`Langlands.Global.Hecke.LatticePoisson`, theorem `tsum_add_intVec_eq_tsum_intFourier`) to a
full lattice `L` in a finite-dimensional real normed space `E`, with respect to an arbitrary
Haar measure `μ` on `E` and an arbitrary nondegenerate bilinear form `B` on `E`. It is an
analytic input for the global (Tate–Hecke) theta functional equation used for the functional
equation of Hecke `L`-functions, where `E` will be the mixed space of a number field, `L` a
fractional ideal and `B` the trace form.

## Provenance

Internal. Poisson summation for a lattice and its dual lattice is classical (e.g. the formula
`∑_{l ∈ L} G(x + l) = covol(L)⁻¹ ∑_{w ∈ L^*} Ĝ(w) e(⟨x, w⟩)` used in Tate's thesis and in
the proof of the functional equation of theta series). The statement here is derived from
the `ℤ^ι` case by a choice of basis. All conventions are Mathlib's:

- `𝐞 t = exp(2πit)` is `Real.fourierChar`;
- the Fourier transform is `VectorFourier.fourierIntegral 𝐞 μ B G w = ∫ v, 𝐞 (-B v w) • G v ∂μ`
  (a Bochner integral, hence `0` when the integrand is not integrable);
- the covolume is `ZLattice.covolume L μ`, the `μ`-measure of a fundamental domain;
- the dual lattice is `B.flip.dualSubmodule L = {w | ∀ l ∈ L, B l w ∈ ℤ}` (Mathlib's
  `LinearMap.BilinForm.dualSubmodule` for the form `B.flip`), which is exactly the set of `w`
  for which `x ↦ 𝐞 (B x w)` is `L`-periodic.

The decay hypothesis used throughout is: `G : E → ℂ` and constants `C, r` with
`(finrank ℝ E : ℝ) < r` and `‖G v‖ ≤ C * (1 + ‖v‖) ^ (-r)` for all `v`.

## Definitions

- `latticeVec b n = b.equivFun.symm (intVec n) = ∑ i, n i • b i` for a basis
  `b : Basis ι ℝ E` and `n : ι → ℤ`.
- `spanEquiv b : (ι → ℤ) ≃ span ℤ (range b)`, `n ↦ latticeVec b n`, with inverse
  `x ↦ (i ↦ ⌊b.repr x i⌋)`.
- `basisCoord b G = G ∘ b.equivFunL.symm : C(ι → ℝ, ℂ)`, the function `G : C(E, ℂ)` read in
  the coordinates of `b`.
- `latticeBasis L = (Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L`, the real basis of `E`
  underlying Mathlib's chosen `ℤ`-basis of the lattice `L` (for `[DiscreteTopology L]`,
  `[IsZLattice ℝ L]`).
- `latticeEquiv L : (ι → ℤ) ≃ L` and `dualLatticeEquiv hB L : (ι → ℤ) ≃ B.flip.dualSubmodule L`
  (with `ι = Free.ChooseBasisIndex ℤ L`), given by `n ↦ latticeVec (latticeBasis L) n` and
  `m ↦ latticeVec (B.flip.dualBasis hB.flip (latticeBasis L)) m`.

## Main results

- `tsum_add_zlattice_eq hB L μ G hr hdecay h_sum x` (**Poisson summation for a lattice**): for
  `G : C(E, ℂ)` with the decay hypothesis and
  `h_sum : Summable fun w : B.flip.dualSubmodule L => VectorFourier.fourierIntegral 𝐞 μ B G w`,

  `∑' l : L, G (x + l) = (ZLattice.covolume L μ)⁻¹ * ∑' w : B.flip.dualSubmodule L, VectorFourier.fourierIntegral 𝐞 μ B G w * 𝐞 (B x w)`.

- `tsum_add_latticeVec_eq μ hB b G hr hdecay h_sum x` (the same for the lattice spanned by a
  basis `b`, with `b' = B.flip.dualBasis hB.flip b`, the basis with `B (b i) (b' j) = δ i j`):

  `∑' n, G (x + latticeVec b n) = (μ.real (parallelepiped b))⁻¹ * ∑' m, 𝓕 G (latticeVec b' m) * 𝐞 (B x (latticeVec b' m))`,

  where `𝓕 G = VectorFourier.fourierIntegral 𝐞 μ B G` and `h_sum` is summability of
  `m ↦ 𝓕 G (latticeVec b' m)`.
- `summable_add_zlattice_of_decay L hr hdecay x : Summable fun l : L => G (x + l)` and
  `summable_dualSubmodule_of_decay hB L hr hdecay : Summable fun w : B.flip.dualSubmodule L => F w`
  (for any `F : E → ℂ` with the decay hypothesis), so that `h_sum` follows from decay of the
  Fourier transform.

Auxiliary results:

- lattice vectors: `latticeVec_eq_sum`, `repr_latticeVec` (`b.repr (latticeVec b n) i = n i`),
  `latticeVec_mem`, `latticeVec_add`, `coe_spanEquiv`, `span_latticeBasis`
  (`span ℤ (range (latticeBasis L)) = L`), `dualSubmodule_eq_span`
  (`B.flip.dualSubmodule L = span ℤ (range (B.flip.dualBasis hB.flip (latticeBasis L)))`),
  `coe_latticeEquiv`, `coe_dualLatticeEquiv`;
- decay: `rpow_neg_le_of_le_mul` (for `0 < a`, `0 < c`, `0 ≤ r` and `a ≤ c * b`:
  `b ^ (-r) ≤ c ^ r * a ^ (-r)`), `nonneg_of_decay` (the decay constant `C` is nonnegative),
  `summable_one_add_norm_latticeVec_rpow` (`∑ n, (1 + ‖latticeVec b n‖) ^ (-r) < ∞` for
  `r > dim E`), `summable_norm_restrict_of_decay` (the translates `basisCoord b G (· + intVec n)`
  are uniformly summable on every compact set), `summable_add_latticeVec_of_decay`;
- coordinates: `basisCoord_apply`, `equivFunL_symm_intVec`, `basisCoord_add_intVec`,
  `basisCoord_equivFunL`;
- measure: `map_equivFunL_eq_smul_volume` (`Measure.map b.equivFunL μ = μ (parallelepiped b) • volume`),
  `measureReal_parallelepiped_pos`, `integral_comp_equivFunL`
  (`∫ v, g (b.equivFunL v) ∂μ = μ.real (parallelepiped b) • ∫ t, g t`),
  `covolume_eq_measureReal_parallelepiped`
  (`ZLattice.covolume L μ = μ.real (parallelepiped (latticeBasis L))`);
- duality: `apply_dualBasis_flip_eq_repr` (`B v (b' j) = b.repr v j`),
  `apply_latticeVec_dualBasis_flip` (`B v (latticeVec b' m) = intDot m (b.equivFunL v)`),
  `intFourier_basisCoord`
  (`intFourier (basisCoord b G) m = (μ.real (parallelepiped b))⁻¹ • 𝓕 G (latticeVec b' m)`).

## Proof

1. *Summability of the lattice zeta series.* `summable_one_add_norm_latticeVec_rpow` applies
   Mathlib's `ZLattice.summable_norm_rpow` to the lattice `span ℤ (range b)` (of rank
   `dim E`, by `ZLattice.rank`), compares `(1 + ‖z‖)^(-r) ≤ ‖z‖^(-r)` for `z ≠ 0`
   (`Real.rpow_le_rpow_of_nonpos`, cofinitely), and reindexes by `spanEquiv b`.
2. *Local uniform summability from decay.* If `‖y‖ ≤ R` then
   `1 + ‖n‖ ≤ (1 + R)(1 + ‖y + n‖)` (triangle inequality), so by `rpow_neg_le_of_le_mul`
   `‖G (y + latticeVec b n)‖ ≤ C (1 + R)^r (1 + ‖latticeVec b n‖)^(-r)`. On a compact set `K` of
   coordinates the vectors `b.equivFunL.symm t` are bounded, which gives
   `summable_norm_restrict_of_decay`; taking `y = x` gives `summable_add_latticeVec_of_decay`.
3. *Change of variables.* `Measure.map b.equivFunL μ` is an additive Haar measure on `ι → ℝ`;
   by uniqueness (`Measure.addHaarMeasure_unique` with the unit cube `PositiveCompacts.piIcc01`
   and `addHaarMeasure_eq_volume_pi`) it equals its value on `[0,1]^ι` times `volume`, and the
   preimage of `[0,1]^ι` is `parallelepiped b` (`parallelepiped_basis_eq`). The parallelepiped
   has positive finite measure (nonempty interior, compact). `integral_comp_equivFunL` follows
   from `integral_map_equiv` and `integral_smul_measure`.
4. *Fourier coefficients.* Writing `b = B.dualBasis hB b'` (`dualBasis_dualBasis_flip`) and
   using `dualBasis_repr_apply`, `B v (b' j) = b.repr v j`; hence
   `B v (latticeVec b' m) = ∑ j, m j * b.repr v j = intDot m (b.equivFunL v)`. Substituting
   into the Fourier integral and applying step 3 gives
   `𝓕 G (latticeVec b' m) = μ.real (parallelepiped b) • intFourier (basisCoord b G) m`, i.e.
   `intFourier_basisCoord`.
5. *Poisson for a basis.* Apply `tsum_add_intVec_eq_tsum_intFourier` to `basisCoord b G` at
   `b.equivFunL x` (its hypotheses are step 2 and, by step 4, `h_sum` scaled by a constant);
   rewrite `basisCoord b G (b.equivFunL x + intVec n) = G (x + latticeVec b n)`, the Fourier
   coefficients by step 4 and `intDot m (b.equivFunL x) = B x (latticeVec b' m)`, and pull
   the constant out of the sum (`tsum_mul_left`).
6. *Poisson for a lattice.* With `b = latticeBasis L`, `span ℤ (range b) = L`
   (`ofZLatticeBasis_span`), and Mathlib's `dualSubmodule_span_of_basis` gives
   `B.flip.dualSubmodule L = span ℤ (range b')`. Reindex both sums by `latticeEquiv L` and
   `dualLatticeEquiv hB L` (`Equiv.tsum_eq`, `Equiv.summable_iff`). The covolume is the
   `μ`-measure of the fundamental domain of `b` (`ZLattice.covolume_eq_measure_fundamentalDomain`
   with `ZLattice.isAddFundamentalDomain`), which is a.e. equal to `parallelepiped b`
   (`ZSpan.fundamentalDomain_ae_parallelepiped`). Step 5 then gives `tsum_add_zlattice_eq`.
   The summability lemmas on `L` and `L^*` are step 2 at `x` (resp. `0`) reindexed by the same
   equivalences.
