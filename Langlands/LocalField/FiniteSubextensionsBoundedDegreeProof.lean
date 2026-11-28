import Langlands.LocalField.FiniteSubextensionsBoundedDegreeStatement
import Langlands.LocalField.AlgebraicExtensionValuation
import Langlands.Galois.Local.SpectralProof
import Langlands.Global.Arithmetic.KrasnerNeighborhood
import Mathlib.Analysis.Normed.Field.Krasner

/-!
# Proof that a characteristic-zero local field has finitely many subextensions of bounded degree

This module proves `Langlands.LocalField.FiniteSubextensionsBoundedDegreeStatement` as
`Langlands.LocalField.finiteSubextensionsBoundedDegree`. The base field `F` carries the norm
`LocalGalois.localNormedField F`, whose topology is the given one, and `AlgebraicClosure F`
carries the spectral norm, for which Mathlib's Krasner lemma (`IsKrasner.of_completeSpace`)
holds over `F`. All auxiliary declarations live in the namespace
`Langlands.LocalField.FiniteSubextensionsBoundedDegree`; the normed structures are local
instances of this file only.

Let `E` be a finite subextension of degree at most `d`.

* The norms of nonzero elements of `E` are integer powers of the norm of an element `ϖ ∈ E`
  with `0 < ‖ϖ‖ < 1` (`exists_valueGenerator`).
* With `q` the residue cardinality of `F` and `M = q ^ d! - 1`, every element of norm one of `E`
  is congruent to an `M`-th root of unity lying in `E` (`norm_pow_rootOrder_sub_one_lt`,
  `exists_rootOfUnity_near`, `rootOfUnity_mem_adjoin`).
* For `U` generated over `F` by all solutions of `ζ ^ M = 1` in `E`, we have `E = U(ϖ)` and
  the minimal polynomial of `ϖ` over `U` is Eisenstein (`exists_eisenstein_generator`, using
  the approximation lemma `mem_of_approx`).
* For each of the finitely many `U` and each degree, compactness of the Eisenstein coefficients
  and Krasner's lemma leave finitely many fields `U(ϖ)` (`finite_eisensteinFields`).

The paired Markdown page describes the proof in detail.
-/

noncomputable section

namespace Langlands.LocalField.FiniteSubextensionsBoundedDegree

open Polynomial IntermediateField

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

local notation "Ω" => AlgebraicClosure F

local instance : NontriviallyNormedField Ω := spectralNorm.nontriviallyNormedField F Ω
local instance : NormedAlgebra F Ω := spectralNorm.normedAlgebra F Ω
local instance : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra F

/-! ### Discreteness of the norm on the base field -/

private theorem localNorm_le_iff_ord_le (x y : F) :
    ‖x‖ ≤ ‖y‖ ↔ FML.ord F y ≤ FML.ord F x := by
  rw [LocalGalois.localNormedField_le, FML.ord_le_ord_iff]
  exact (Valuation.Compatible.vle_iff_le x y).symm

private theorem localNorm_eq_of_ord_eq {x y : F}
    (h : FML.ord F x = FML.ord F y) : ‖x‖ = ‖y‖ := by
  apply le_antisymm
  · exact (localNorm_le_iff_ord_le F x y).mpr h.ge
  · exact (localNorm_le_iff_ord_le F y x).mpr h.le

theorem baseNorm_lt_one : ‖uniformizer F‖ < 1 := by
  have ho : FML.ord F 1 < FML.ord F (uniformizer F) := by simp
  have h : ‖uniformizer F‖ < ‖(1 : F)‖ := by
    rw [lt_iff_not_ge, localNorm_le_iff_ord_le F]
    exact not_le.mpr ho
  simpa using h

theorem baseNorm_pos : 0 < ‖uniformizer F‖ :=
  norm_pos_iff.mpr (uniformizer_ne_zero F)

private theorem uniformizerUnit_order :
    (Plancherel.fieldOrderUnits F (Units.mk0 (uniformizer F) (uniformizer_ne_zero F))).toAdd
      = 1 := by
  apply WithTop.coe_injective
  rw [← Plancherel.fieldOrderUnits_ord]
  exact ord_uniformizer F

/-- Every nonzero element of the base field has norm an integer power of the norm of the
uniformizer. -/
theorem baseNorm_eq_zpow (a : F) (ha : a ≠ 0) :
    ∃ k : ℤ, ‖a‖ = ‖uniformizer F‖ ^ k := by
  let p : Fˣ := Units.mk0 (uniformizer F) (uniformizer_ne_zero F)
  let u : Fˣ := Units.mk0 a ha
  let n : ℤ := (Plancherel.fieldOrderUnits F u).toAdd
  have hp : (Plancherel.fieldOrderUnits F p).toAdd = 1 := uniformizerUnit_order F
  have hn : FML.ord F ((p ^ n : Fˣ) : F) = FML.ord F (u : F) := by
    rw [Plancherel.fieldOrderUnits_ord, Plancherel.fieldOrderUnits_ord, map_zpow,
      toAdd_zpow, hp]
    simp [n]
  have hn' := localNorm_eq_of_ord_eq F hn
  refine ⟨n, ?_⟩
  simpa only [Units.val_zpow_eq_zpow_val, norm_zpow, p, u, Units.val_mk0] using hn'.symm

/-! ### Norms of algebraic elements -/

theorem norm_pow_natDegree (x : Ω) :
    ‖x‖ ^ (minpoly F x).natDegree = ‖(minpoly F x).coeff 0‖ := by
  have h : ‖x‖ = ‖(minpoly F x).coeff 0‖ ^ (1 / (minpoly F x).natDegree : ℝ) :=
    spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := F) (L := Ω) x
  have hm : (minpoly F x).natDegree ≠ 0 :=
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := F) x)).ne'
  rw [h, one_div, Real.rpow_inv_natCast_pow (norm_nonneg _) hm]

/-- For `D > 0`, the `D`-th root of the norm of the uniformizer. -/
def sig (D : ℕ) : ℝ := ‖uniformizer F‖ ^ ((D : ℝ)⁻¹)

theorem sig_pos (D : ℕ) : 0 < sig F D := Real.rpow_pos_of_pos (baseNorm_pos F) _

theorem sig_pow {D : ℕ} (hD : D ≠ 0) : sig F D ^ D = ‖uniformizer F‖ :=
  Real.rpow_inv_natCast_pow (baseNorm_pos F).le hD

theorem sig_lt_one {D : ℕ} (hD : D ≠ 0) : sig F D < 1 := by
  have h := sig_pow F hD
  by_contra hc
  have : (1 : ℝ) ≤ sig F D ^ D := one_le_pow₀ (not_lt.mp hc)
  linarith [baseNorm_lt_one F]

/-- For `D > 0`, a nonzero algebraic element whose degree divides `D` has norm an integer power
of `sig F D`. -/
theorem norm_eq_sig_zpow {D : ℕ} (hD : D ≠ 0) (x : Ω) (hx : x ≠ 0)
    (hdeg : (minpoly F x).natDegree ∣ D) : ∃ j : ℤ, ‖x‖ = sig F D ^ j := by
  have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  obtain ⟨c, hc⟩ := hdeg
  set m := (minpoly F x).natDegree with hm
  have hm0 : m ≠ 0 := (minpoly.natDegree_pos hint).ne'
  obtain ⟨k, hk⟩ := baseNorm_eq_zpow F _ (minpoly.coeff_zero_ne_zero hint hx)
  refine ⟨(c : ℤ) * k, ?_⟩
  have hpow : ‖x‖ ^ m = (sig F D ^ ((c : ℤ) * k)) ^ m := by
    rw [norm_pow_natDegree, hk, ← sig_pow F hD, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, hc]
    congr 1
    push_cast
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_pos (sig_pos F D) _).le hm0).mp hpow

theorem natDegree_le_finrank (E : IntermediateField F Ω) [FiniteDimensional F E]
    {x : Ω} (hx : x ∈ E) : (minpoly F x).natDegree ≤ Module.finrank F E := by
  have := minpoly.natDegree_le (A := F) (B := E) (⟨x, hx⟩ : E)
  rwa [IntermediateField.minpoly_eq] at this

/-! ### A value generator for a finite subextension -/

/-- Every finite subextension `K` has an element `ϖ` with `0 < ‖ϖ‖ < 1` whose norm generates
the norms of all nonzero elements of `K`. -/
theorem exists_valueGenerator (K : IntermediateField F Ω) [FiniteDimensional F K] :
    ∃ ϖ ∈ K, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ ∀ x ∈ K, x ≠ 0 → ∃ j : ℤ, ‖x‖ = ‖ϖ‖ ^ j := by
  classical
  set D := (Module.finrank F K).factorial with hDdef
  have hD : D ≠ 0 := Nat.factorial_ne_zero _
  have hdeg : ∀ x ∈ K, (minpoly F x).natDegree ∣ D := fun x hx =>
    Nat.dvd_factorial (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral (R := F) x))
      (natDegree_le_finrank F K hx)
  have hval : ∀ x ∈ K, x ≠ 0 → ∃ j : ℤ, ‖x‖ = sig F D ^ j := fun x hx hx0 =>
    norm_eq_sig_zpow F hD x hx0 (hdeg x hx)
  have hex : ∃ n : ℕ, 0 < n ∧ ∃ x ∈ K, ‖x‖ = sig F D ^ (n : ℤ) :=
    ⟨D, Nat.pos_of_ne_zero hD, algebraMap F Ω (uniformizer F), K.algebraMap_mem _, by
      rw [norm_algebraMap', zpow_natCast, sig_pow F hD]⟩
  obtain ⟨hg0, ϖ, hϖK, hϖ⟩ := Nat.find_spec hex
  set g := Nat.find hex with hgdef
  refine ⟨ϖ, hϖK, ?_, ?_, ?_⟩
  · rw [hϖ]; exact zpow_pos (sig_pos F D) _
  · rw [hϖ, zpow_natCast]; exact pow_lt_one₀ (sig_pos F D).le (sig_lt_one F hD) hg0.ne'
  · intro x hx hx0
    obtain ⟨j, hj⟩ := hval x hx hx0
    have hgz : (0 : ℤ) < g := by exact_mod_cast hg0
    have hr0 : 0 ≤ j % (g : ℤ) := Int.emod_nonneg _ hgz.ne'
    have hrg : j % (g : ℤ) < g := Int.emod_lt_of_pos _ hgz
    have hjqr : (g : ℤ) * (j / g) + j % g = j := Int.mul_ediv_add_emod j g
    by_cases hr : j % (g : ℤ) = 0
    · refine ⟨j / g, ?_⟩
      rw [hj, hϖ, ← zpow_mul]
      congr 1
      omega
    · exfalso
      have hy : x * ϖ ^ (-(j / (g : ℤ))) ∈ K := K.mul_mem hx (zpow_mem hϖK _)
      have hny : ‖x * ϖ ^ (-(j / (g : ℤ)))‖ = sig F D ^ (((j % (g : ℤ)).toNat : ℕ) : ℤ) := by
        rw [norm_mul, norm_zpow, hj, hϖ, ← zpow_mul, ← zpow_add₀ (sig_pos F D).ne',
          Int.toNat_of_nonneg hr0]
        congr 1
        linarith
      have hlt : (j % (g : ℤ)).toNat < g := by omega
      exact Nat.find_min hex hlt ⟨by omega, _, hy, hny⟩

/-! ### Distance to a finite-dimensional subspace -/

/-- Let `V` be a finite-dimensional subspace. If each `v ∈ V` at positive distance from `x`
admits a closer point in `V`, and every such improvement reduces the distance to at most
`c * ‖x - v‖` for a fixed `0 < c < 1`, then `x ∈ V`. -/
theorem mem_of_approx (V : Submodule F Ω) [FiniteDimensional F V] (x : Ω) {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1)
    (hdisc : ∀ v ∈ V, ∀ w ∈ V, x - v ≠ 0 → ‖x - w‖ < ‖x - v‖ → ‖x - w‖ ≤ c * ‖x - v‖)
    (happrox : ∀ v ∈ V, x - v ≠ 0 → ∃ w ∈ V, ‖x - w‖ < ‖x - v‖) : x ∈ V := by
  by_contra hx
  have hne : (V : Set Ω).Nonempty := ⟨0, V.zero_mem⟩
  have hclosed : IsClosed (V : Set Ω) := Submodule.closed_of_finiteDimensional V
  have hδ : 0 < Metric.infDist x (V : Set Ω) := (hclosed.notMem_iff_infDist_pos hne).mp hx
  set δ := Metric.infDist x (V : Set Ω)
  have hlt : δ < δ / c := by
    rw [lt_div_iff₀ hc0]
    nlinarith
  obtain ⟨v, hv, hvd⟩ := (Metric.infDist_lt_iff hne).mp hlt
  have hxv : x - v ≠ 0 := fun h => hx (by rw [sub_eq_zero.mp h]; exact hv)
  obtain ⟨w, hw, hwlt⟩ := happrox v hv hxv
  have h1 := hdisc v hv w hw hxv hwlt
  have h2 : δ ≤ ‖x - w‖ := by
    rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem hw
  rw [dist_eq_norm, lt_div_iff₀ hc0] at hvd
  nlinarith

/-! ### Roots of unity of order prime to the residue characteristic -/

section RootsOfUnity


local notation "𝒪Ω" => LocalGalois.extensionIntegers F Ω
local notation "kF" => IsLocalRing.ResidueField (LocalGalois.baseIntegers F)
local notation "κ" => IsLocalRing.ResidueField (LocalGalois.extensionIntegers F Ω)

local instance : Finite kF := LocalGalois.localResidue_finite F
local instance : Fintype kF := Fintype.ofFinite _

theorem mem_integers_iff (x : Ω) : x ∈ LocalGalois.extensionIntegers F Ω ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
  rfl

theorem mem_maximalIdeal_iff (a : 𝒪Ω) :
    a ∈ IsLocalRing.maximalIdeal 𝒪Ω ↔ ‖(a : Ω)‖ < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one, ← NNReal.coe_lt_coe]
  rfl

/-- The common exponent `q ^ d! - 1` for the roots of unity used as residue representatives,
where `q` is the residue cardinality of `F`. -/
def rootOrder (d : ℕ) : ℕ := Fintype.card kF ^ d.factorial - 1

theorem norm_rootOrder (d : ℕ) : ‖((rootOrder F d : ℕ) : Ω)‖ = 1 := by
  set n := rootOrder F d
  have hle : ‖(n : Ω)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one Ω n
  have hk : (n : kF) = -1 := by
    simp only [n, rootOrder]
    rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow,
      FiniteField.cast_card_eq_zero, zero_pow (Nat.factorial_ne_zero _), Nat.cast_one, zero_sub]
  have hres : IsLocalRing.residue 𝒪Ω (n : 𝒪Ω) ≠ 0 := by
    rw [map_natCast, ← map_natCast (algebraMap kF κ), hk, map_neg, map_one]
    exact neg_ne_zero.mpr one_ne_zero
  rw [Ne, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff] at hres
  have hcast : (((n : 𝒪Ω) : Ω)) = (n : Ω) := by simp
  rw [hcast] at hres
  exact le_antisymm hle (not_lt.mp hres)

theorem rootOrder_ne_zero (d : ℕ) : rootOrder F d ≠ 0 := by
  intro h
  have := norm_rootOrder F d
  rw [h, Nat.cast_zero, norm_zero] at this
  exact zero_ne_one this

/-- An element of norm one and degree at most `d` over `F` has `rootOrder F d`-th power
congruent to `1` modulo the maximal ideal of the valuation ring of `Ω`. -/
theorem norm_pow_rootOrder_sub_one_lt (d : ℕ) (u : Ω) (hu : ‖u‖ = 1)
    (hdeg : (minpoly F u).natDegree ≤ d) : ‖u ^ rootOrder F d - 1‖ < 1 := by
  classical
  set D := d.factorial
  set q := Fintype.card kF
  have hint : IsIntegral F u := Algebra.IsIntegral.isIntegral u
  let a : 𝒪Ω := ⟨u, (mem_integers_iff F u).mpr hu.le⟩
  have hm := minpoly.monic hint
  have hcoeff : ∀ n, ‖(minpoly F u).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp hu.le
  have hlift : minpoly F u ∈ lifts (algebraMap (LocalGalois.baseIntegers F) F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨g, hg, hgdeg, hgm⟩ := lifts_and_degree_eq_and_monic hlift hm
  have hga : aeval a g = 0 := by
    have h := minpoly.aeval F u
    rw [← hg, aeval_def, eval₂_map] at h
    have hcomp : (algebraMap 𝒪Ω Ω).comp (algebraMap (LocalGalois.baseIntegers F) 𝒪Ω) =
        (algebraMap F Ω).comp (algebraMap (LocalGalois.baseIntegers F) F) := rfl
    have h' : algebraMap 𝒪Ω Ω (aeval a g) = 0 := by
      rw [aeval_def, hom_eval₂, hcomp]
      exact h
    exact (map_eq_zero_iff _ (IsFractionRing.injective 𝒪Ω Ω)).mp h'
  set ub := IsLocalRing.residue 𝒪Ω a
  have hroot : aeval ub (g.map (IsLocalRing.residue (LocalGalois.baseIntegers F))) = 0 := by
    rw [aeval_def, eval₂_map]
    have hcomp : (algebraMap kF κ).comp (IsLocalRing.residue (LocalGalois.baseIntegers F)) =
        (IsLocalRing.residue 𝒪Ω).comp (algebraMap (LocalGalois.baseIntegers F) 𝒪Ω) := rfl
    rw [hcomp, ← hom_eval₂, ← aeval_def, hga, map_zero]
  have hubint : IsIntegral kF ub := Algebra.IsIntegral.isIntegral ub
  have hfle : (minpoly kF ub).natDegree ≤ d := by
    have hmin := minpoly.min kF ub (hgm.map _) hroot
    have := natDegree_le_natDegree hmin
    rw [hgm.natDegree_map, natDegree_eq_of_degree_eq hgdeg] at this
    exact this.trans hdeg
  set f := (minpoly kF ub).natDegree
  have hf0 : 0 < f := minpoly.natDegree_pos hubint
  have hfD : f ∣ D := Nat.dvd_factorial hf0 hfle
  have : FiniteDimensional kF kF⟮ub⟯ := IntermediateField.adjoin.finiteDimensional hubint
  have : Finite kF⟮ub⟯ := Module.finite_of_finite kF
  let : Fintype kF⟮ub⟯ := Fintype.ofFinite _
  have hcard : Fintype.card kF⟮ub⟯ = q ^ f := by
    rw [Module.card_eq_pow_finrank (K := kF), IntermediateField.adjoin.finrank hubint]
  obtain ⟨c, hc⟩ := hfD
  have hpow : ub ^ (q ^ D) = ub := by
    have h := FiniteField.pow_card_pow c (⟨ub, IntermediateField.mem_adjoin_simple_self kF ub⟩ :
      kF⟮ub⟯)
    rw [hcard, ← pow_mul, ← hc] at h
    exact congrArg Subtype.val h
  have hres : IsLocalRing.residue 𝒪Ω (a ^ (q ^ D) - a) = 0 := by
    rw [map_sub, map_pow, hpow, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff] at hres
  have hqD : q ^ D = rootOrder F d + 1 :=
    (Nat.sub_add_cancel (Nat.one_le_pow _ _ Fintype.card_pos)).symm
  have hcoe : ((a ^ (q ^ D) - a : 𝒪Ω) : Ω) = u * (u ^ rootOrder F d - 1) := by
    push_cast
    rw [hqD, pow_succ]
    simp only [a]
    ring
  rw [hcoe, norm_mul, hu, one_mul] at hres
  exact hres

theorem norm_eq_one_of_pow_eq_one (d : ℕ) {z : Ω} (hz : z ^ rootOrder F d = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ rootOrder F d = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (rootOrder_ne_zero F d)).mp this

/-- Distinct solutions of `ζ ^ M = 1` for `M = rootOrder F d` are at distance one. -/
theorem norm_sub_eq_one_of_pow_eq_one (d : ℕ) {ζ ζ' : Ω} (hζ : ζ ^ rootOrder F d = 1)
    (hζ' : ζ' ^ rootOrder F d = 1) (hne : ζ ≠ ζ') : ‖ζ - ζ'‖ = 1 := by
  set M := rootOrder F d
  have hM0 : M ≠ 0 := rootOrder_ne_zero F d
  have hn := norm_eq_one_of_pow_eq_one F d hζ
  have hn' := norm_eq_one_of_pow_eq_one F d hζ'
  have h1 : ‖ζ - ζ'‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg, hn, hn', max_self]
  refine le_antisymm h1 (not_lt.mp fun hlt => ?_)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  set η := ζ' / ζ
  have hη : η ^ M = 1 := by rw [div_pow, hζ, hζ', div_one]
  have hη1 : η ≠ 1 := by
    intro h
    apply hne
    have : ζ' = η * ζ := by simp [η, hζ0]
    rw [this, h, one_mul]
  have hηn : ‖η‖ = 1 := by rw [norm_div, hn, hn', div_one]
  have hsum : ∑ i ∈ Finset.range M, η ^ i = 0 := by
    rw [geom_sum_eq hη1, hη, sub_self, zero_div]
  have hd : ‖η - 1‖ < 1 := by
    have : η - 1 = -((ζ - ζ') / ζ) := by
      rw [show η = ζ' / ζ from rfl]
      field_simp
      ring
    rw [this, norm_neg, norm_div, hn, div_one]
    exact hlt
  have hpow : ∀ i : ℕ, ‖η ^ i - 1‖ < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : η ^ (i + 1) - 1 = η * (η ^ i - 1) + (η - 1) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hd)
      rw [norm_mul, hηn, one_mul]
      exact ih
  have hlt1 : ‖(M : Ω)‖ < 1 := by
    have heq : (M : Ω) = -(∑ i ∈ Finset.range M, (η ^ i - 1)) := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    rw [heq, norm_neg]
    obtain ⟨i, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      (Finset.nonempty_range_iff.mpr hM0) (fun i => η ^ i - 1)
    exact hle.trans_lt (hpow i)
  rw [norm_rootOrder F d] at hlt1
  exact lt_irrefl _ hlt1

/-- If the `M`-th power of `u` is congruent to `1` for `M = rootOrder F d`, there is an
`M`-th root of unity `ζ` with `‖u - ζ‖ < 1`. -/
theorem exists_rootOfUnity_near (d : ℕ) {u : Ω} (h : ‖u ^ rootOrder F d - 1‖ < 1) :
    ∃ ζ : Ω, ζ ^ rootOrder F d = 1 ∧ ‖u - ζ‖ < 1 := by
  classical
  set M := rootOrder F d
  have hM0 : M ≠ 0 := rootOrder_ne_zero F d
  have hmon : (X ^ M - C (1 : Ω)).Monic := monic_X_pow_sub_C _ hM0
  have hsplit := IsAlgClosed.splits (X ^ M - C (1 : Ω))
  have heval := hsplit.eval_eq_prod_roots_of_monic hmon u
  simp only [eval_sub, eval_pow, eval_X, eval_C] at heval
  by_contra hcon
  push Not at hcon
  have hge : ∀ ζ ∈ (X ^ M - C (1 : Ω)).roots, (1 : NNReal) ≤ ‖u - ζ‖₊ := by
    intro ζ hζ
    have hζ' : ζ ^ M = 1 := by
      have := (mem_roots hmon.ne_zero).mp hζ
      simpa [sub_eq_zero] using this
    have := hcon ζ hζ'
    rw [← NNReal.coe_le_coe]
    simpa using this
  have h1 : (1 : NNReal) ≤ ‖u ^ M - 1‖₊ := by
    rw [heval, Multiset.nnnorm_prod_map]
    apply Multiset.one_le_prod_of_one_le
    intro x hx
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
    exact hge ζ hζ
  have h2 : (1 : ℝ) ≤ ‖u ^ M - 1‖ := by
    rw [← coe_nnnorm]
    exact_mod_cast h1
  linarith

/-- In characteristic zero, Krasner's lemma places any `M`-th root of unity `ζ` with
`‖u - ζ‖ < 1` in `F⟮u⟯`, where `M = rootOrder F d`. -/
theorem rootOfUnity_mem_adjoin [CharZero F] (d : ℕ) {u ζ : Ω} (hζ : ζ ^ rootOrder F d = 1)
    (h : ‖u - ζ‖ < 1) : ζ ∈ F⟮u⟯ := by
  have hsep : (minpoly F ζ).Separable := Algebra.IsSeparable.isSeparable F ζ
  refine IsKrasner.krasner hsep (IsAlgClosed.splits _) (Algebra.IsIntegral.isIntegral u) ?_
  intro ζ' hc hne
  have hζ' : ζ' ^ rootOrder F d = 1 := by
    obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hc
    have h1 : σ (ζ' ^ rootOrder F d) = σ 1 := by rw [map_pow, hσ, hζ, map_one]
    exact σ.injective h1
  rw [norm_sub_eq_one_of_pow_eq_one F d hζ hζ' hne, norm_sub_rev]
  exact h

end RootsOfUnity

/-! ### Conjugates and coefficients of minimal polynomials -/

theorem norm_eq_of_isConjRoot {x y : Ω} (h : IsConjRoot F x y) : ‖x‖ = ‖y‖ := by
  obtain ⟨σ, hσ⟩ := h.exists_algEquiv
  rw [← hσ]
  exact (spectralNorm_eq_of_equiv σ y).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isIntegral_of_intermediate (K : IntermediateField F Ω) (x : Ω) : IsIntegral K x :=
  (Algebra.IsIntegral.isIntegral (R := F) x).tower_top

/-- Every root of the minimal polynomial of `x` over an intermediate field has the norm of `x`. -/
theorem norm_root_minpoly (K : IntermediateField F Ω) {x y : Ω}
    (hy : y ∈ ((minpoly K x).map (algebraMap K Ω)).roots) : ‖y‖ = ‖x‖ := by
  have hc : IsConjRoot K x y :=
    (isConjRoot_iff_mem_minpoly_aroots (isIntegral_of_intermediate F K x)).mpr hy
  have hcF : IsConjRoot F x y := hc.of_isScalarTower (Algebra.IsIntegral.isIntegral x)
  exact (norm_eq_of_isConjRoot F hcF).symm

/-- The constant coefficient of the minimal polynomial over an intermediate field has norm
`‖x‖ ^ deg`. -/
theorem norm_coeff_zero_minpoly (K : IntermediateField F Ω) (x : Ω) :
    ‖((minpoly K x).coeff 0 : Ω)‖ = ‖x‖ ^ (minpoly K x).natDegree := by
  have hint := isIntegral_of_intermediate F K x
  set p := (minpoly K x).map (algebraMap K Ω) with hp
  have hm : p.Monic := (minpoly.monic hint).map _
  have hs : p.Splits := IsAlgClosed.splits p
  have h0 : p.coeff 0 = ((minpoly K x).coeff 0 : Ω) := by
    rw [hp, coeff_map]
    rfl
  have hroots : ∀ y ∈ p.roots, ‖y‖ = ‖x‖ := fun y hy => norm_root_minpoly F K hy
  rw [← h0, hs.coeff_zero_eq_prod_roots_of_monic hm, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Multiset.norm_prod, Multiset.map_congr rfl hroots, Multiset.map_const',
    Multiset.prod_replicate, ← hs.natDegree_eq_card_roots, hp, natDegree_map]

/-- A product of factors `X - C y` with `‖y‖ < 1` has all coefficients in the closed unit
ball and all non-leading coefficients in the open unit ball. -/
theorem norm_coeff_prod_lt_one (s : Multiset Ω) (hs : ∀ y ∈ s, ‖y‖ < 1) :
    (∀ i, ‖((s.map fun y => X - C y).prod).coeff i‖ ≤ 1) ∧
      ∀ i < Multiset.card s, ‖((s.map fun y => X - C y).prod).coeff i‖ < 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    refine ⟨fun i => ?_, fun i hi => absurd hi (by simp)⟩
    simp only [Multiset.map_zero, Multiset.prod_zero, coeff_one]
    split_ifs <;> simp
  | cons a t ih =>
    have ha : ‖a‖ < 1 := hs a (Multiset.mem_cons_self a t)
    obtain ⟨ih1, ih2⟩ := ih fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    set Q := (t.map fun y => X - C y).prod
    have hP : ((a ::ₘ t).map fun y => X - C y).prod = Q * (X - C a) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
    rw [hP]
    have h0 : ‖(Q * (X - C a)).coeff 0‖ < 1 := by
      rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg, norm_neg,
        norm_mul]
      calc ‖Q.coeff 0‖ * ‖a‖ ≤ 1 * ‖a‖ :=
            mul_le_mul_of_nonneg_right (ih1 0) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact ha
    have hsucc : ∀ i, ‖(Q * (X - C a)).coeff (i + 1)‖ ≤
        max ‖Q.coeff i‖ (‖Q.coeff (i + 1)‖ * ‖a‖) := by
      intro i
      rw [coeff_mul_X_sub_C, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_mul]
    have hprod : ∀ i, ‖Q.coeff (i + 1)‖ * ‖a‖ < 1 := fun i =>
      calc ‖Q.coeff (i + 1)‖ * ‖a‖ ≤ 1 * ‖a‖ :=
            mul_le_mul_of_nonneg_right (ih1 _) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact ha
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · rcases i with _ | i
      · exact h0.le
      · exact (hsucc i).trans (max_le (ih1 i) (hprod i).le)
    · rcases i with _ | i
      · exact h0
      · rw [Multiset.card_cons] at hi
        exact (hsucc i).trans_lt (max_lt (ih2 i (by omega)) (hprod i))

/-- If `‖x‖ < 1`, the non-leading coefficients of its minimal polynomial over an intermediate
field lie in the open unit ball. -/
theorem norm_coeff_minpoly_lt_one (K : IntermediateField F Ω) {x : Ω} (hx : ‖x‖ < 1)
    {i : ℕ} (hi : i < (minpoly K x).natDegree) : ‖((minpoly K x).coeff i : Ω)‖ < 1 := by
  have hint := isIntegral_of_intermediate F K x
  set p := (minpoly K x).map (algebraMap K Ω) with hp
  have hm : p.Monic := (minpoly.monic hint).map _
  have hs : p.Splits := IsAlgClosed.splits p
  have hroots : ∀ y ∈ p.roots, ‖y‖ < 1 := fun y hy => by
    rw [norm_root_minpoly F K hy]
    exact hx
  have hcard : (minpoly K x).natDegree = Multiset.card p.roots := by
    rw [← hs.natDegree_eq_card_roots, hp, natDegree_map]
  have h := (norm_coeff_prod_lt_one F p.roots hroots).2 i (hcard ▸ hi)
  rw [← hs.eq_prod_roots_of_monic hm, hp, coeff_map] at h
  exact h

/-! ### Eisenstein polynomials over an intermediate field -/

section Eisenstein

/-- A monic polynomial over `U` whose non-leading coefficients have norm at most `r` and whose
constant coefficient has norm exactly `r`. -/
def IsEis (U : IntermediateField F Ω) (r : ℝ) (g : Polynomial U) : Prop :=
  g.Monic ∧ (∀ i : ℕ, i < g.natDegree → ‖(g.coeff i : Ω)‖ ≤ r) ∧ ‖(g.coeff 0 : Ω)‖ = r

/-- The norm of `c • β ^ i` for `c` in an intermediate field. -/
theorem norm_smul_pow {U : IntermediateField F Ω} {c : U} {β : Ω} (i : ℕ) :
    ‖c • β ^ i‖ = ‖(c : Ω)‖ * ‖β‖ ^ i := by
  rw [Algebra.smul_def, norm_mul, norm_pow]
  rfl

/-- If `0 < ρ < 1`, each root of a positive-degree polynomial satisfying `IsEis F U ρ` has
norm whose `m`-th power is `ρ`, where `m` is the degree of the polynomial. -/
theorem norm_pow_of_isEis {U : IntermediateField F Ω} {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {g : Polynomial U} (hg : IsEis F U ρ g) (hm : 0 < g.natDegree) {β : Ω}
    (hβ : aeval β g = 0) : ‖β‖ ^ g.natDegree = ρ := by
  obtain ⟨hmon, hle, h0⟩ := hg
  set m := g.natDegree with hmdef
  have hsum : ∑ i ∈ Finset.range (m + 1), g.coeff i • β ^ i = 0 := by
    rw [← aeval_eq_sum_range]
    exact hβ
  set t := ‖β‖
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases lt_trichotomy (t ^ m) ρ with hlt | heq | hgt
  · exfalso
    have ht1 : t < 1 := by
      by_contra h
      have : (1 : ℝ) ≤ t ^ m := one_le_pow₀ (not_lt.mp h)
      linarith
    rw [Finset.sum_range_succ'] at hsum
    have hc0 : g.coeff 0 • β ^ 0 = -∑ i ∈ Finset.range m, g.coeff (i + 1) • β ^ (i + 1) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum
    have hbound : ‖∑ i ∈ Finset.range m, g.coeff (i + 1) • β ^ (i + 1)‖ < ρ := by
      obtain ⟨i, hi, hle'⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hm.ne') (fun i => g.coeff (i + 1) • β ^ (i + 1))
      refine hle'.trans_lt ?_
      rw [norm_smul_pow F]
      have hti : t ^ (i + 1) < 1 := pow_lt_one₀ ht0 ht1 (Nat.succ_ne_zero i)
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt (Finset.mem_range.mp hi)) with hlt' | heq'
      · calc ‖(g.coeff (i + 1) : Ω)‖ * t ^ (i + 1) ≤ ρ * t ^ (i + 1) :=
              mul_le_mul_of_nonneg_right (hle _ hlt') (pow_nonneg ht0 _)
          _ < ρ := mul_lt_of_lt_one_right hρ0 hti
      · have hi1 : i + 1 = m := heq'
        rw [hi1, hmdef, hmon.coeff_natDegree, OneMemClass.coe_one, norm_one, one_mul]
        exact hlt
    have h1 := congrArg norm hc0
    rw [norm_neg, norm_smul_pow F, pow_zero, mul_one, h0] at h1
    linarith
  · exact heq
  · exfalso
    rw [Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hsum
    have hcm : β ^ m = -∑ i ∈ Finset.range m, g.coeff i • β ^ i := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hsum
    have hbound : ‖∑ i ∈ Finset.range m, g.coeff i • β ^ i‖ < t ^ m := by
      obtain ⟨i, hi, hle'⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hm.ne') (fun i => g.coeff i • β ^ i)
      refine hle'.trans_lt ?_
      rw [norm_smul_pow F]
      have hi' := Finset.mem_range.mp hi
      calc ‖(g.coeff i : Ω)‖ * t ^ i ≤ ρ * t ^ i :=
            mul_le_mul_of_nonneg_right (hle i hi') (pow_nonneg ht0 _)
        _ < t ^ m := by
          rcases le_or_gt t 1 with ht1 | ht1
          · calc ρ * t ^ i ≤ ρ * 1 :=
                  mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) hρ0.le
              _ < t ^ m := by rw [mul_one]; exact hgt
          · calc ρ * t ^ i < 1 * t ^ i :=
                  mul_lt_mul_of_pos_right hρ1 (pow_pos (by linarith) _)
              _ ≤ t ^ m := by
                  rw [one_mul]
                  exact pow_le_pow_right₀ ht1.le hi'.le
    have := congrArg norm hcm
    rw [norm_neg, norm_pow] at this
    linarith

/-- Assume `0 < ρ < 1` and that every nonzero norm on `U` is an integer power of `ρ`.
A root of a positive-degree polynomial satisfying `IsEis F U ρ` has the same degree over
`U` as the polynomial. -/
theorem natDegree_minpoly_of_isEis {U : IntermediateField F Ω} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hρ : ∀ x : Ω, x ∈ U → x ≠ 0 → ∃ j : ℤ, ‖x‖ = ρ ^ j) {g : Polynomial U}
    (hg : IsEis F U ρ g) (hm : 0 < g.natDegree) {β : Ω} (hβ : aeval β g = 0) :
    (minpoly U β).natDegree = g.natDegree := by
  have hpow := norm_pow_of_isEis F hρ0 hρ1 hg hm hβ
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow hm.ne'] at hpow
    linarith
  have hint := isIntegral_of_intermediate F U β
  have hdvd : minpoly U β ∣ g := minpoly.dvd U β hβ
  have hle : (minpoly U β).natDegree ≤ g.natDegree := natDegree_le_of_dvd hdvd hg.1.ne_zero
  have hpos : 0 < (minpoly U β).natDegree := minpoly.natDegree_pos hint
  have hc0 : ((minpoly U β).coeff 0 : Ω) ≠ 0 := by
    have := minpoly.coeff_zero_ne_zero hint hβ0
    exact_mod_cast this
  obtain ⟨j, hj⟩ := hρ _ ((minpoly U β).coeff 0).2 hc0
  rw [norm_coeff_zero_minpoly] at hj
  have h1 : ρ ^ ((minpoly U β).natDegree : ℤ) = ρ ^ (j * g.natDegree) := by
    calc ρ ^ ((minpoly U β).natDegree : ℤ)
        = (‖β‖ ^ g.natDegree) ^ (minpoly U β).natDegree := by rw [zpow_natCast, hpow]
      _ = (‖β‖ ^ (minpoly U β).natDegree) ^ g.natDegree := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ρ ^ (j * g.natDegree) := by rw [hj, zpow_mul, zpow_natCast]
  have h2 : ((minpoly U β).natDegree : ℤ) = j * g.natDegree :=
    zpow_right_injective₀ hρ0 hρ1.ne h1
  have hj1 : 1 ≤ j := by
    by_contra hc
    have : j * (g.natDegree : ℤ) ≤ 0 :=
      Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
    omega
  have : (g.natDegree : ℤ) ≤ (minpoly U β).natDegree := by
    rw [h2]
    nlinarith
  omega

end Eisenstein

/-! ### Krasner neighbourhoods of Eisenstein coefficient vectors -/

/-- The monic polynomial of degree `m` with lower coefficients `a`. -/
def coeffPoly {m : ℕ} (a : Fin m → Ω) : Polynomial Ω :=
  X ^ m + ∑ i : Fin m, C (a i) * X ^ (i : ℕ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffPoly_monic {m : ℕ} (a : Fin m → Ω) : (coeffPoly F a).Monic :=
  monic_X_pow_add (degree_sum_fin_lt a)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffPoly_natDegree {m : ℕ} (a : Fin m → Ω) : (coeffPoly F a).natDegree = m := by
  unfold coeffPoly
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt a

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffPoly_eval {m : ℕ} (a : Fin m → Ω) (y : Ω) :
    (coeffPoly F a).eval y = y ^ m + ∑ i : Fin m, a i * y ^ (i : ℕ) := by
  simp [coeffPoly, eval_finsetSum]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem coeffPoly_coeff {m : ℕ} (a : Fin m → Ω) {i : ℕ} (hi : i < m) :
    (coeffPoly F a).coeff i = a ⟨i, hi⟩ := by
  classical
  unfold coeffPoly
  rw [coeff_add, coeff_X_pow, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Fintype.sum_eq_single ⟨i, hi⟩]
  · simp [Nat.ne_of_lt hi]
  · intro j hj
    have : i ≠ (j : ℕ) := fun h => hj (Fin.ext h.symm)
    simp [this]

/-- Lower coefficient vectors of degree-`m` polynomials satisfying `IsEis F U ρ`. -/
def eisSet (U : IntermediateField F Ω) (ρ : ℝ) (m : ℕ) (hm : 0 < m) : Set (Fin m → Ω) :=
  {a | (∀ i, a i ∈ U ∧ ‖a i‖ ≤ ρ) ∧ ‖a ⟨0, hm⟩‖ = ρ}

theorem exists_lift_of_mem_eisSet {U : IntermediateField F Ω} {ρ : ℝ} {m : ℕ} {hm : 0 < m}
    {a : Fin m → Ω} (ha : a ∈ eisSet F U ρ m hm) :
    ∃ Q : Polynomial U, Q.map (algebraMap U Ω) = coeffPoly F a ∧ IsEis F U ρ Q ∧
      Q.natDegree = m := by
  let b : Fin m → U := fun i => ⟨a i, (ha.1 i).1⟩
  let Q : Polynomial U := X ^ m + ∑ i : Fin m, C (b i) * X ^ (i : ℕ)
  have hQm : Q.Monic := monic_X_pow_add (degree_sum_fin_lt b)
  have hmap : Q.map (algebraMap U Ω) = coeffPoly F a := by
    simp only [Q, coeffPoly, Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C]
    rfl
  have hQd : Q.natDegree = m := by
    have := congrArg natDegree hmap
    rwa [natDegree_map, coeffPoly_natDegree] at this
  have hcoeff : ∀ i (hi : i < m), (Q.coeff i : Ω) = a ⟨i, hi⟩ := by
    intro i hi
    have := congrArg (fun p => coeff p i) hmap
    simp only [coeff_map] at this
    rw [coeffPoly_coeff F a hi] at this
    exact this
  refine ⟨Q, hmap, ⟨hQm, fun i hi => ?_, ?_⟩, hQd⟩
  · rw [hQd] at hi
    rw [hcoeff i hi]
    exact (ha.1 _).2
  · rw [hcoeff 0 hm]
    exact ha.2

/-- The minimum of `1` and the conjugate radii over `F` of the roots of `coeffPoly F a`. -/
def krasnerRadius {m : ℕ} (a : Fin m → Ω) : ℝ := by
  classical
  exact (insert 1 ((coeffPoly F a).roots.toFinset.image
    (Langlands.Global.FieldRealization.conjugateRadius F))).inf' (by simp) id

theorem krasnerRadius_pos {m : ℕ} (a : Fin m → Ω) : 0 < krasnerRadius F a := by
  classical
  unfold krasnerRadius
  rw [Finset.lt_inf'_iff]
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hr
  · norm_num
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hr
    exact Langlands.Global.FieldRealization.conjugateRadius_pos y

theorem krasnerRadius_le {m : ℕ} (a : Fin m → Ω) {β : Ω} (hβ : β ∈ (coeffPoly F a).roots) :
    krasnerRadius F a ≤ Langlands.Global.FieldRealization.conjugateRadius F β := by
  classical
  unfold krasnerRadius
  apply Finset.inf'_le id
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨β, Multiset.mem_toFinset.mpr hβ, rfl⟩

/-- Assume `F` has characteristic zero, `0 < ρ < 1` and every nonzero norm on `U` is an integer
power of `ρ`. For `a ∈ eisSet F U ρ m hm`, let `Q` be monic of degree `m` over `U` with each
lower coefficient at distance less than `krasnerRadius F a ^ m` from the corresponding entry
of `a`. Each root of `Q` of norm at most one generates the same field over `U` as some root
of `coeffPoly F a`. -/
theorem adjoin_eq_of_close [CharZero F] {U : IntermediateField F Ω} {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hρ : ∀ x : Ω, x ∈ U → x ≠ 0 → ∃ j : ℤ, ‖x‖ = ρ ^ j) {m : ℕ} (hm : 0 < m)
    {a : Fin m → Ω} (ha : a ∈ eisSet F U ρ m hm) {Q : Polynomial U} (hQm : Q.Monic)
    (hQd : Q.natDegree = m) (hQ : ∀ i : Fin m, ‖a i - (Q.coeff i : Ω)‖ < krasnerRadius F a ^ m)
    {y : Ω} (hy : aeval y Q = 0) (hy1 : ‖y‖ ≤ 1) :
    ∃ β ∈ (coeffPoly F a).roots,
      IntermediateField.adjoin U {y} = IntermediateField.adjoin U {β} := by
  set r := krasnerRadius F a with hr
  have hr0 : 0 < r := krasnerRadius_pos F a
  set P := coeffPoly F a with hP
  have hPm : P.Monic := coeffPoly_monic F a
  have hPs : P.Splits := IsAlgClosed.splits P
  -- the value of `P` at `y` is small
  have hQy : y ^ m + ∑ i ∈ Finset.range m, (Q.coeff i : Ω) * y ^ i = 0 := by
    have h := hy
    rw [hQm.as_sum, hQd] at h
    simpa [aeval_def, eval₂_finsetSum] using h
  have heval : P.eval y = ∑ i : Fin m, (a i - (Q.coeff i : Ω)) * y ^ (i : ℕ) := by
    rw [coeffPoly_eval]
    have h2 : ∑ i : Fin m, (Q.coeff i : Ω) * y ^ (i : ℕ) =
        ∑ i ∈ Finset.range m, (Q.coeff i : Ω) * y ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (Q.coeff i : Ω) * y ^ i) m
    simp only [sub_mul, Finset.sum_sub_distrib, h2]
    linear_combination hQy
  have hsmall : ‖P.eval y‖ < r ^ m := by
    rw [heval]
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩
    obtain ⟨i, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun i : Fin m => (a i - (Q.coeff i : Ω)) * y ^ (i : ℕ))
    refine hle.trans_lt ?_
    rw [norm_mul, norm_pow]
    calc ‖a i - (Q.coeff i : Ω)‖ * ‖y‖ ^ (i : ℕ) ≤ ‖a i - (Q.coeff i : Ω)‖ * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hy1) (norm_nonneg _)
      _ < r ^ m := by rw [mul_one]; exact hQ i
  -- hence `y` is close to a root of `P`
  have hcard : Multiset.card P.roots = m := by
    rw [← hPs.natDegree_eq_card_roots, hP, coeffPoly_natDegree]
  obtain ⟨β, hβ, hyβ⟩ : ∃ β ∈ P.roots, ‖y - β‖ < r := by
    by_contra hcon
    push Not at hcon
    let r' : NNReal := ⟨r, hr0.le⟩
    have hge : r' ^ Multiset.card (P.roots.map fun β => ‖y - β‖₊) ≤
        (P.roots.map fun β => ‖y - β‖₊).prod := by
      apply Multiset.pow_card_le_prod
      intro x hx
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hx
      rw [← NNReal.coe_le_coe]
      exact hcon β hβ
    rw [Multiset.card_map, ← Multiset.nnnorm_prod_map, ← hPs.eval_eq_prod_roots_of_monic hPm,
      hcard] at hge
    have : r ^ m ≤ ‖P.eval y‖ := by
      rw [← coe_nnnorm]
      exact_mod_cast hge
    linarith
  -- Krasner's lemma over the base field
  have hβF : β ∈ F⟮y⟯ := by
    refine IsKrasner.krasner (Algebra.IsSeparable.isSeparable F β) (IsAlgClosed.splits _)
      (Algebra.IsIntegral.isIntegral y) ?_
    intro β' hc hne
    calc ‖β - y‖ = ‖y - β‖ := norm_sub_rev _ _
      _ < r := hyβ
      _ ≤ Langlands.Global.FieldRealization.conjugateRadius F β := krasnerRadius_le F a hβ
      _ ≤ ‖β - β'‖ := Langlands.Global.FieldRealization.conjugateRadius_le β β'
          (Algebra.IsIntegral.isIntegral β) hc hne
  have hβU : β ∈ IntermediateField.adjoin U {y} := by
    have hle : F⟮y⟯ ≤ (IntermediateField.adjoin U {y}).restrictScalars F := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self U y
    exact hle hβF
  have hle : IntermediateField.adjoin U {β} ≤ IntermediateField.adjoin U {y} :=
    IntermediateField.adjoin_simple_le_iff.mpr hβU
  -- degree comparison
  obtain ⟨Qa, hQa, hQaEis, hQad⟩ := exists_lift_of_mem_eisSet F ha
  have hβroot : aeval β Qa = 0 := by
    have := (mem_roots hPm.ne_zero).mp hβ
    rw [IsRoot, hP, ← hQa, eval_map_algebraMap] at this
    exact this
  have hdβ : (minpoly U β).natDegree = m := by
    rw [natDegree_minpoly_of_isEis F hρ0 hρ1 hρ hQaEis (hQad ▸ hm) hβroot, hQad]
  have hdy : (minpoly U y).natDegree ≤ m := by
    rw [← hQd]
    exact natDegree_le_of_dvd (minpoly.dvd U y hy) hQm.ne_zero
  have hintβ := isIntegral_of_intermediate F U β
  have hinty := isIntegral_of_intermediate F U y
  have : FiniteDimensional U (IntermediateField.adjoin U {y}) :=
    IntermediateField.adjoin.finiteDimensional hinty
  refine ⟨β, hβ, (IntermediateField.eq_of_le_of_finrank_le hle ?_).symm⟩
  rw [IntermediateField.adjoin.finrank hintβ, IntermediateField.adjoin.finrank hinty, hdβ]
  exact hdy

theorem isCompact_eisSet (U : IntermediateField F Ω) [FiniteDimensional F U] (ρ : ℝ) {m : ℕ}
    (hm : 0 < m) : IsCompact (eisSet F U ρ m hm) := by
  let W : Submodule F Ω := U.toSubalgebra.toSubmodule
  have : FiniteDimensional F W := ‹FiniteDimensional F U›
  have : ProperSpace W := FiniteDimensional.proper F W
  have hB : IsCompact {x : Ω | x ∈ U ∧ ‖x‖ ≤ ρ} := by
    have heq : {x : Ω | x ∈ U ∧ ‖x‖ ≤ ρ} = Subtype.val '' Metric.closedBall (0 : W) ρ := by
      ext x
      constructor
      · rintro ⟨hxU, hxρ⟩
        exact ⟨⟨x, hxU⟩, by simpa using hxρ, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, by simpa using hw⟩
    rw [heq]
    exact (isCompact_closedBall _ _).image continuous_subtype_val
  have hpi : IsCompact (Set.pi Set.univ fun _ : Fin m => {x : Ω | x ∈ U ∧ ‖x‖ ≤ ρ}) :=
    isCompact_univ_pi fun _ => hB
  have hcl : IsClosed {a : Fin m → Ω | ‖a ⟨0, hm⟩‖ = ρ} :=
    isClosed_eq (continuous_apply _).norm continuous_const
  have heq : eisSet F U ρ m hm =
      (Set.pi Set.univ fun _ : Fin m => {x : Ω | x ∈ U ∧ ‖x‖ ≤ ρ}) ∩
        {a : Fin m → Ω | ‖a ⟨0, hm⟩‖ = ρ} := by
    ext a
    simp [eisSet, Set.mem_pi]
  rw [heq]
  exact hpi.inter_right hcl

/-- Assume `F` has characteristic zero, `U` is finite-dimensional over `F`, and every nonzero
norm on `U` is an integer power of `ρ` with `0 < ρ < 1`. For each `m > 0`, there are finitely many
subfields of `Ω` of the form `U⟮ϖ⟯` with `‖ϖ‖ ≤ 1` and minimal polynomial of degree `m`
satisfying `IsEis F U ρ`. -/
theorem finite_eisensteinFields [CharZero F] (U : IntermediateField F Ω) [FiniteDimensional F U]
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hρ : ∀ x : Ω, x ∈ U → x ≠ 0 → ∃ j : ℤ, ‖x‖ = ρ ^ j)
    {m : ℕ} (hm : 0 < m) :
    {E : IntermediateField F Ω | ∃ ϖ : Ω, ‖ϖ‖ ≤ 1 ∧ IsEis F U ρ (minpoly U ϖ) ∧
      (minpoly U ϖ).natDegree = m ∧
        E = (IntermediateField.adjoin U {ϖ}).restrictScalars F}.Finite := by
  classical
  obtain ⟨t, htC, hcover⟩ := (isCompact_eisSet F U ρ hm).elim_nhds_subcover
    (fun a => Metric.ball a (krasnerRadius F a ^ m))
    (fun a _ => Metric.ball_mem_nhds a (pow_pos (krasnerRadius_pos F a) m))
  refine Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun a _ =>
    Set.Finite.biUnion (coeffPoly F a).roots.toFinset.finite_toSet fun β _ =>
      Set.finite_singleton ((IntermediateField.adjoin U {β}).restrictScalars F)) ?_
  rintro E ⟨ϖ, hϖ1, hEis, hdeg, rfl⟩
  let c : Fin m → Ω := fun i => ((minpoly U ϖ).coeff i : Ω)
  have hc : c ∈ eisSet F U ρ m hm :=
    ⟨fun i => ⟨((minpoly U ϖ).coeff i).2, hEis.2.1 i (hdeg ▸ i.2)⟩, hEis.2.2⟩
  obtain ⟨a, hat, hca⟩ := Set.mem_iUnion₂.mp (hcover hc)
  rw [Metric.mem_ball, dist_pi_lt_iff (pow_pos (krasnerRadius_pos F a) m)] at hca
  obtain ⟨β, hβ, heq⟩ := adjoin_eq_of_close F hρ0 hρ1 hρ hm (htC a hat) hEis.1 hdeg
    (fun i => by rw [← dist_eq_norm, dist_comm]; exact hca i) (minpoly.aeval U ϖ) hϖ1
  refine Set.mem_biUnion (Finset.mem_coe.mpr hat)
    (Set.mem_biUnion (Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr hβ)) ?_)
  rw [heq]
  rfl

/-! ### Structure of a finite subextension -/

/-- Over a characteristic-zero base `F`, let `E` be a finite subextension of degree at most
`d`. Let `S` be a finite subset of `E` containing every `M`-th root of unity in `E` for
`M = rootOrder F d`, and let `U = F(S)`. Suppose `πU ∈ U` has `0 < ‖πU‖ < 1` and every
nonzero norm on `U` is an integer power of `‖πU‖`. Then there is `ϖ` of norm at most one
whose minimal polynomial over `U` satisfies `IsEis F U ‖πU‖` and has degree between `1`
and `d`, with `E = (U⟮ϖ⟯).restrictScalars F`. -/
theorem exists_eisenstein_generator [CharZero F] {d : ℕ} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : Module.finrank F E ≤ d) (S : Finset Ω)
    (hSE : ∀ ζ ∈ S, ζ ∈ E) (hS : ∀ ζ : Ω, ζ ^ rootOrder F d = 1 → ζ ∈ E → ζ ∈ S)
    {πU : Ω} (hπU : πU ∈ IntermediateField.adjoin F (S : Set Ω)) (hπ0 : 0 < ‖πU‖)
    (hπ1 : ‖πU‖ < 1)
    (hval : ∀ x : Ω, x ∈ IntermediateField.adjoin F (S : Set Ω) → x ≠ 0 →
      ∃ j : ℤ, ‖x‖ = ‖πU‖ ^ j) :
    ∃ ϖ : Ω, ‖ϖ‖ ≤ 1 ∧
      IsEis F (IntermediateField.adjoin F (S : Set Ω)) ‖πU‖
        (minpoly (IntermediateField.adjoin F (S : Set Ω)) ϖ) ∧
      0 < (minpoly (IntermediateField.adjoin F (S : Set Ω)) ϖ).natDegree ∧
      (minpoly (IntermediateField.adjoin F (S : Set Ω)) ϖ).natDegree ≤ d ∧
      E = (IntermediateField.adjoin (IntermediateField.adjoin F (S : Set Ω)) {ϖ}).restrictScalars
        F := by
  classical
  set U := IntermediateField.adjoin F (S : Set Ω) with hUdef
  set ρ := ‖πU‖ with hρdef
  have hUE : U ≤ E := IntermediateField.adjoin_le_iff.mpr fun ζ hζ => hSE ζ hζ
  have : FiniteDimensional F U :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨ϖ, hϖE, hϖ0, hϖ1, hvalE⟩ := exists_valueGenerator F E
  set r := ‖ϖ‖ with hrdef
  have hdegE : ∀ x ∈ E, (minpoly F x).natDegree ≤ d := fun x hx =>
    (natDegree_le_finrank F E hx).trans hE
  -- `ρ = r ^ e` with `e ≥ 1`
  obtain ⟨e0, he0⟩ := hvalE πU (hUE hπU) (norm_pos_iff.mp hπ0)
  have he0pos : 0 < e0 := by
    by_contra h
    have : 1 ≤ r ^ e0 := one_le_zpow_of_nonpos₀ hϖ0 hϖ1.le (not_lt.mp h)
    rw [← he0] at this
    linarith
  set e := e0.toNat with hedef
  have he : e0 = (e : ℤ) := (Int.toNat_of_nonneg he0pos.le).symm
  have hepos : 0 < e := by omega
  have hρe : ρ = r ^ e := by rw [hρdef, he0, he, zpow_natCast]
  -- the `U`-span of `1, ϖ, …, ϖ ^ (e - 1)`
  let V : Submodule U Ω := Submodule.span U (Set.range fun t : Fin e => ϖ ^ (t : ℕ))
  have hVfg : (V.restrictScalars F).FG :=
    (Submodule.fg_span (Set.finite_range _)).restrictScalars
  have : FiniteDimensional F (V.restrictScalars F) :=
    (Submodule.fg_iff_finiteDimensional _).mp hVfg
  have : Module.Finite U V := Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))
  have hVE : ∀ v ∈ V, v ∈ E := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact pow_mem hϖE _
    | zero => exact E.zero_mem
    | add x y _ _ hx hy => exact E.add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact E.mul_mem (hUE c.2) hx
  -- every element of `E` lies in `V`
  have hEV : ∀ x ∈ E, x ∈ V := by
    intro x hx
    have hmem := mem_of_approx F (V.restrictScalars F) x hϖ0 hϖ1 ?_ ?_
    · exact hmem
    · intro v hv w hw hxv hlt
      have hvE : x - v ∈ E := E.sub_mem hx (hVE v hv)
      have hwE : x - w ∈ E := E.sub_mem hx (hVE w hw)
      by_cases hxw : x - w = 0
      · rw [hxw, norm_zero]
        exact mul_nonneg hϖ0.le (norm_nonneg _)
      obtain ⟨a, ha⟩ := hvalE _ hvE hxv
      obtain ⟨b, hb⟩ := hvalE _ hwE hxw
      rw [ha, hb, zpow_lt_zpow_iff_right_of_lt_one₀ hϖ0 hϖ1] at hlt
      rw [ha, hb, ← zpow_one_add₀ hϖ0.ne']
      exact zpow_le_zpow_right_of_le_one₀ hϖ0 hϖ1.le (by omega)
    · intro v hv hxv
      have hyE : x - v ∈ E := E.sub_mem hx (hVE v hv)
      obtain ⟨j, hj⟩ := hvalE _ hyE hxv
      set q := j / (e : ℤ)
      set t := j % (e : ℤ)
      have ht0 : 0 ≤ t := Int.emod_nonneg _ (by exact_mod_cast hepos.ne')
      have hte : t < e := Int.emod_lt_of_pos _ (by exact_mod_cast hepos)
      have hjqt : (e : ℤ) * q + t = j := Int.mul_ediv_add_emod j e
      set c : Ω := πU ^ q * ϖ ^ t.toNat with hcdef
      have hπne : πU ≠ 0 := norm_pos_iff.mp hπ0
      have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
      have hc0 : c ≠ 0 := mul_ne_zero (zpow_ne_zero _ hπne) (pow_ne_zero _ hϖne)
      have hcE : c ∈ E := E.mul_mem (zpow_mem (hUE hπU) _) (pow_mem hϖE _)
      have hcnorm : ‖c‖ = ‖x - v‖ := by
        rw [hcdef, norm_mul, norm_zpow, norm_pow, ← hρdef, hρe, hj, ← zpow_natCast,
          ← zpow_natCast r t.toNat, Int.toNat_of_nonneg ht0, ← zpow_mul, ← zpow_add₀ hϖ0.ne',
          ← hjqt]
      set u := (x - v) / c with hudef
      have huE : u ∈ E := E.div_mem hyE hcE
      have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
      have hu : ‖u‖ = 1 := by
        rw [hudef, norm_div, hcnorm, div_self (norm_pos_iff.mpr hxv).ne']
      obtain ⟨ζ, hζM, hζu⟩ := exists_rootOfUnity_near F d
        (norm_pow_rootOrder_sub_one_lt F d u hu (hdegE u huE))
      have hζE : ζ ∈ E :=
        (IntermediateField.adjoin_simple_le_iff.mpr huE) (rootOfUnity_mem_adjoin F d hζM hζu)
      have hζU : ζ ∈ U :=
        IntermediateField.subset_adjoin F _ (Finset.mem_coe.mpr (hS ζ hζM hζE))
      have hcoef : ζ * πU ^ q ∈ U := U.mul_mem hζU (zpow_mem hπU _)
      refine ⟨v + ζ * c, ?_, ?_⟩
      · have hmemV : ζ * c ∈ V := by
          have h1 : ζ * c =
              (⟨ζ * πU ^ q, hcoef⟩ : U) • ϖ ^ ((⟨t.toNat, by omega⟩ : Fin e) : ℕ) := by
            rw [Algebra.smul_def]
            simp only [IntermediateField.algebraMap_apply, hcdef]
            ring
          rw [h1]
          exact V.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        exact (V.restrictScalars F).add_mem hv hmemV
      · have hxw : x - (v + ζ * c) = c * (u - ζ) := by
          rw [hudef]
          field_simp
          ring
        rw [hxw, norm_mul, ← hcnorm]
        calc ‖c‖ * ‖u - ζ‖ < ‖c‖ * 1 := mul_lt_mul_of_pos_left hζu hcpos
          _ = ‖c‖ := mul_one _
  -- `E = U(ϖ)`
  have hadjE : IntermediateField.adjoin U {ϖ} ≤ IntermediateField.extendScalars hUE :=
    IntermediateField.adjoin_simple_le_iff.mpr ((IntermediateField.mem_extendScalars hUE).mpr hϖE)
  have hVadj : ∀ v ∈ V, v ∈ IntermediateField.adjoin U {ϖ} := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      exact pow_mem (IntermediateField.mem_adjoin_simple_self U ϖ) _
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x _ hx =>
      rw [Algebra.smul_def]
      exact mul_mem (IntermediateField.algebraMap_mem _ c) hx
  have hEeq : E = (IntermediateField.adjoin U {ϖ}).restrictScalars F := by
    ext x
    constructor
    · intro hx
      exact hVadj x (hEV x hx)
    · intro hx
      exact (IntermediateField.mem_extendScalars hUE).mp (hadjE hx)
  -- the degree of `ϖ` over `U`
  have hintU := isIntegral_of_intermediate F U ϖ
  set m := (minpoly U ϖ).natDegree with hmdef
  have hmpos : 0 < m := minpoly.natDegree_pos hintU
  have hmle : m ≤ e := by
    have hle : (IntermediateField.adjoin U {ϖ}).toSubalgebra.toSubmodule ≤ V := by
      intro x hx
      exact hEV x ((IntermediateField.mem_extendScalars hUE).mp (hadjE hx))
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank U V ≤ e := by
      have := finrank_range_le_card (R := U) (fun t : Fin e => ϖ ^ (t : ℕ))
      simpa [Set.finrank] using this
    rw [hmdef, ← IntermediateField.adjoin.finrank hintU]
    exact h1.trans h2
  have hc0ne : ((minpoly U ϖ).coeff 0 : Ω) ≠ 0 := by
    have := minpoly.coeff_zero_ne_zero hintU (norm_pos_iff.mp hϖ0)
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hval _ ((minpoly U ϖ).coeff 0).2 hc0ne
  rw [norm_coeff_zero_minpoly, ← hmdef, hρe, ← zpow_natCast, ← zpow_natCast,
    ← zpow_mul] at hk
  have hmk : (m : ℤ) = e * k := zpow_right_injective₀ hϖ0 hϖ1.ne hk
  have hk1 : 1 ≤ k := by
    by_contra h
    have : (e : ℤ) * k ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
    omega
  have hme : m = e := by
    have : (e : ℤ) ≤ m := by rw [hmk]; nlinarith
    omega
  refine ⟨ϖ, hϖ1.le, ⟨minpoly.monic hintU, ?_, ?_⟩, hmpos, ?_, hEeq⟩
  · intro i hi
    have hlt := norm_coeff_minpoly_lt_one F U hϖ1 hi
    by_cases hz : ((minpoly U ϖ).coeff i : Ω) = 0
    · rw [hz, norm_zero]
      exact hπ0.le
    obtain ⟨l, hl⟩ := hval _ ((minpoly U ϖ).coeff i).2 hz
    rw [hl] at hlt ⊢
    have hl1 : 1 ≤ l := by
      by_contra h
      have : 1 ≤ ρ ^ l := one_le_zpow_of_nonpos₀ hπ0 hπ1.le (by omega)
      linarith
    calc ρ ^ l ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hπ0 hπ1.le hl1
      _ = ρ := zpow_one ρ
  · rw [norm_coeff_zero_minpoly, ← hmdef, hme, hρe]
  · have hdvd := minpoly.dvd_map_of_isScalarTower F U ϖ
    have h1 := natDegree_le_of_dvd hdvd
      ((Polynomial.map_ne_zero_iff (algebraMap F U).injective).mpr
        (minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := F) ϖ)))
    rw [natDegree_map] at h1
    exact h1.trans (hdegE ϖ hϖE)

/-! ### Assembly -/

universe u

/-- The union over the finitely many choices of `U = F(S)` and of the degree `m` of
`finite_eisensteinFields` contains every subextension of degree at most `d`. -/
theorem finite_boundedDegree : FiniteSubextensionsBoundedDegreeStatement.{u} := by
  intro F _ _ _ _ _ d
  classical
  set R := nthRootsFinset (rootOrder F d) (1 : AlgebraicClosure F)
  have key : ∀ S : Finset (AlgebraicClosure F), ∃ π : AlgebraicClosure F,
      π ∈ IntermediateField.adjoin F (S : Set (AlgebraicClosure F)) ∧ 0 < ‖π‖ ∧ ‖π‖ < 1 ∧
      ∀ x : AlgebraicClosure F, x ∈ IntermediateField.adjoin F (S : Set (AlgebraicClosure F)) →
        x ≠ 0 → ∃ j : ℤ, ‖x‖ = ‖π‖ ^ j := by
    intro S
    have : FiniteDimensional F (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    obtain ⟨π, hπ, h0, h1, hv⟩ :=
      exists_valueGenerator F (IntermediateField.adjoin F (S : Set (AlgebraicClosure F)))
    exact ⟨π, hπ, h0, h1, hv⟩
  choose π hπU hπ0 hπ1 hπval using key
  have hfin : ∀ S ∈ R.powerset, ∀ m ∈ Finset.Icc 1 d,
      {E : IntermediateField F (AlgebraicClosure F) | ∃ ϖ : AlgebraicClosure F, ‖ϖ‖ ≤ 1 ∧
        IsEis F (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) ‖π S‖
          (minpoly (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) ϖ) ∧
        (minpoly (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) ϖ).natDegree = m ∧
        E = (IntermediateField.adjoin
          (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) {ϖ}).restrictScalars
            F}.Finite := by
    intro S _ m hm
    have : FiniteDimensional F (IntermediateField.adjoin F (S : Set (AlgebraicClosure F))) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
    exact finite_eisensteinFields F _ (hπ0 S) (hπ1 S) (hπval S) (Finset.mem_Icc.mp hm).1
  refine (Set.Finite.biUnion R.powerset.finite_toSet fun S hS =>
    Set.Finite.biUnion (Finset.Icc 1 d).finite_toSet fun m hm => hfin S hS m hm).subset ?_
  rintro E ⟨hfd, hdeg⟩
  have : FiniteDimensional F E := hfd
  set S := R.filter (· ∈ E) with hSdef
  have hM : 0 < rootOrder F d := Nat.pos_of_ne_zero (rootOrder_ne_zero F d)
  obtain ⟨ϖ, hϖ1, hEis, hpos, hle, hEq⟩ := exists_eisenstein_generator F hdeg S
    (fun ζ hζ => (Finset.mem_filter.mp hζ).2)
    (fun ζ hζM hζE => Finset.mem_filter.mpr ⟨(mem_nthRootsFinset hM _).mpr hζM, hζE⟩)
    (hπU S) (hπ0 S) (hπ1 S) (hπval S)
  exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _)))
    (Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hpos, hle⟩))
      ⟨ϖ, hϖ1, hEis, rfl, hEq⟩)

end Langlands.LocalField.FiniteSubextensionsBoundedDegree

namespace Langlands.LocalField

universe u

/-- **Finitely many subextensions of bounded degree.** For every characteristic-zero
nonarchimedean local field `F` and every `d : ℕ`, the intermediate fields of
`AlgebraicClosure F / F` that are finite-dimensional over `F` of degree at most `d` form a
finite set. -/
theorem finiteSubextensionsBoundedDegree : FiniteSubextensionsBoundedDegreeStatement.{u} :=
  FiniteSubextensionsBoundedDegree.finite_boundedDegree

end Langlands.LocalField
