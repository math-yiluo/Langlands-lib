import Langlands.Global.Hecke.MixedSpaceFourier
import Langlands.Global.AdeleQuotientCompactProof
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.ClassField.Global.FiniteDivisorFractionalIdeal
import Langlands.LocalFactor.Abelian.TateFunctionalEquation
import Langlands.LocalFactor.Harmonic.NormalizationProof
import Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
import Langlands.Global.Factors.HeckeAdditiveConductors

/-!
# Lattices of a number field with prescribed local components

Let `K` be a number field. For a finite place `v` the completion `K_v` carries the local-field
data `CompletionPadic.topologicalData v`, whose valuation lattices are
`L_v(m) = π_v^{-m} O_v` (`additiveLattice m`). This module collects the arithmetic of the
global lattices cut out by such local conditions:

* the discrete valuation of `topologicalData v` restricts to the `v`-adic valuation of `K`
  (`discreteValuation_algebraMap`);
* for a finitely supported `m`, the fractional ideal `latticeIdeal m = ∏ 𝔭_v^{-m v}` consists
  exactly of the `γ ∈ K` lying in `L_v(m v)` for every `v` (`mem_latticeIdeal_iff`), and
  `N(latticeIdeal m) = ∏ N(𝔭_v)^{-m v}` (`absNorm_latticeIdeal`);
* strong approximation: finitely many local conditions `γ ∈ c_v + L_v(m_v)` together with
  integrality at all other places have a common solution `γ ∈ K` (`exists_approx`);
* a self-dual Haar measure for a character of conductor `n` gives `O` the mass `q^{-n/2}`, so
  `μ(L(m)) μ(L(n - m)) = 1` (`measure_additiveLattice_mul_measure_dual`);
* for archimedean scales `aR, aC` and finite characters `ψ_v` satisfying the additive product
  formula (`AdditiveProductFormula`), and conductors `n_v ≥ 0` outside a finite set: the
  conductors vanish outside a finite set (`finite_setOf_additiveConductor_ne_zero`), the
  trace-dual of the lattice of `latticeIdeal m` in the mixed space is the lattice of
  `latticeIdeal (n - m)` (`dualSubmodule_idealLattice`), and the Tamagawa normalization
  `κ covol(Λ_m) ∏_{v ∈ S} μ_v(L_v(m_v)) = 1` holds
  (`mixedGaussianConst_mul_covolume_mul_prod_latticeMass`).
-/

noncomputable section

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global.CompletionPadic
open scoped NumberField nonZeroDivisors WithZero
open Module NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real FourierTransform

namespace Langlands.Global.Hecke

variable {K : Type*} [Field K] [NumberField K]

/-! ### Valuations of global elements -/

section Valuation

/-- The valuation lattices of `topologicalData v` are described by the completion valuation. -/
theorem mem_additiveLattice_iff_valued (v : FinitePlace K) (x : FiniteCompletion K v) (k : ℤ) :
    x ∈ (topologicalData v).additiveLattice k ↔ Valued.v x ≤ WithZero.exp k := by
  rw [PadicField.TopologicalData.mem_additiveLattice,
    AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation]

/-- The discrete valuation of `topologicalData v` restricts to the `v`-adic valuation of `K`. -/
theorem discreteValuation_algebraMap (v : FinitePlace K) (γ : K) :
    (topologicalData v).discreteValuation (algebraMap K (FiniteCompletion K v) γ) =
      v.valuation K γ := by
  rw [AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation]
  exact valuedAdicCompletion_eq_valuation' v γ

theorem algebraMap_mem_additiveLattice_iff (v : FinitePlace K) (γ : K) (k : ℤ) :
    algebraMap K (FiniteCompletion K v) γ ∈ (topologicalData v).additiveLattice k ↔
      v.valuation K γ ≤ WithZero.exp k := by
  rw [PadicField.TopologicalData.mem_additiveLattice, discreteValuation_algebraMap]

/-- The level-zero lattice of `topologicalData v` is the ring of integers of the completion. -/
theorem mem_additiveLattice_zero_iff (v : FinitePlace K) (x : FiniteCompletion K v) :
    x ∈ (topologicalData v).additiveLattice 0 ↔ x ∈ v.adicCompletionIntegers K := by
  rw [mem_additiveLattice_iff_valued, mem_adicCompletionIntegers, WithZero.exp_zero]

/-- A global element is integral at all but finitely many places. -/
theorem finite_setOf_not_mem_additiveLattice_zero (γ : K) :
    {v : FinitePlace K | algebraMap K (FiniteCompletion K v) γ ∉
      (topologicalData v).additiveLattice 0}.Finite := by
  refine (HeightOneSpectrum.Support.finite (𝓞 K) γ).subset fun v hv => ?_
  rw [Set.mem_ofPred_eq, algebraMap_mem_additiveLattice_iff, WithZero.exp_zero, not_le] at hv
  exact hv

end Valuation

/-! ### Fractional ideals with prescribed local lattices -/

section LatticeIdeal

/-- The valuation of a nonzero element is `exp (-count)` of its principal fractional ideal. -/
theorem valuation_eq_exp_neg_count (v : FinitePlace K) {a : K} (ha : a ≠ 0) :
    v.valuation K a = WithZero.exp
      (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ a)) := by
  obtain ⟨n, d, rfl⟩ := IsLocalization.exists_mk'_eq (𝓞 K)⁰ a
  have hn : n ≠ 0 := by
    intro hn
    apply ha
    rw [hn, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hI : FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha
  have hrepr : FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K n d) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((algebraMap (𝓞 K) K) d)⁻¹ *
        ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  rw [FractionalIdeal.count_well_defined K v hI hrepr, valuation_of_mk',
    intValuation_if_neg _ hn, intValuation_if_neg _ (nonZeroDivisors.coe_ne_zero d),
    ← WithZero.exp_sub]
  congr 1
  ring

/-- A nonzero fractional ideal `J` is contained in a nonzero fractional ideal `I` as soon as all
multiplicities of `J` are at least those of `I`. -/
theorem le_of_forall_count_le {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : FinitePlace K, FractionalIdeal.count K v I ≤ FractionalIdeal.count K v J) :
    J ≤ I := by
  have hJI : J * I⁻¹ ≠ 0 := mul_ne_zero hJ (inv_ne_zero hI)
  have hle : J * I⁻¹ ≤ 1 := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJI]
    apply finprod_induction (p := fun X : FractionalIdeal (𝓞 K)⁰ K => X ≤ 1)
    · exact le_rfl
    · intro x y hx hy
      calc x * y ≤ x * 1 := mul_le_mul_right hy x
        _ = x := mul_one x
        _ ≤ 1 := hx
    · intro w
      have hc : 0 ≤ FractionalIdeal.count K w (J * I⁻¹) := by
        rw [FractionalIdeal.count_mul K w hJ (inv_ne_zero hI), FractionalIdeal.count_inv]
        linarith [h w]
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hc
      rw [hk, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
      exact FractionalIdeal.coeIdeal_le_one
  calc J = J * I⁻¹ * I := by rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
    _ ≤ 1 * I := mul_le_mul_left hle I
    _ = I := one_mul I

/-- The fractional ideal `∏ 𝔭_v^{-m v}` of the finitely supported level vector `m`. Its elements
are the `γ ∈ K` with `γ ∈ π_v^{-m v} O_v` for every finite place `v`. -/
def latticeIdeal (m : FinitePlace K →₀ ℤ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  ClassField.Global.finiteDivisorFractionalIdeal K (-m)

theorem count_latticeIdeal (m : FinitePlace K →₀ ℤ) (v : FinitePlace K) :
    FractionalIdeal.count K v (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) = -m v := by
  rw [latticeIdeal, ← ClassField.Global.fractionalIdealDivisor_apply,
    ClassField.Global.fractionalIdealDivisor_finiteDivisorFractionalIdeal, Finsupp.neg_apply]

/-- Membership in `latticeIdeal m` is the conjunction of the local conditions. -/
theorem mem_latticeIdeal_iff (m : FinitePlace K →₀ ℤ) (γ : K) :
    γ ∈ (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : FinitePlace K, v.valuation K γ ≤ WithZero.exp (m v) := by
  by_cases hγ : γ = 0
  · subst hγ
    simp only [map_zero, zero_le, implies_true, iff_true]
    exact Submodule.zero_mem _
  have hI : (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := Units.ne_zero _
  have hJ : FractionalIdeal.spanSingleton (𝓞 K)⁰ γ ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hγ
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp_rw [valuation_eq_exp_neg_count _ hγ, WithZero.exp_le_exp]
  constructor
  · intro hle v
    have := FractionalIdeal.count_mono K v hJ hle
    rw [count_latticeIdeal] at this
    linarith
  · intro h
    apply le_of_forall_count_le hI hJ
    intro v
    rw [count_latticeIdeal]
    linarith [h v]

/-- Membership in `latticeIdeal m` through the local valuation lattices. -/
theorem mem_latticeIdeal_iff_forall_mem (m : FinitePlace K →₀ ℤ) (γ : K) :
    γ ∈ (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ v : FinitePlace K, algebraMap K (FiniteCompletion K v) γ ∈
        (topologicalData v).additiveLattice (m v) := by
  rw [mem_latticeIdeal_iff]
  exact forall_congr' fun v => (algebraMap_mem_additiveLattice_iff v γ (m v)).symm

/-- `N(∏ 𝔭_v^{-m v}) = ∏ N(𝔭_v)^{-m v}`. -/
theorem absNorm_latticeIdeal (m : FinitePlace K →₀ ℤ) :
    FractionalIdeal.absNorm (latticeIdeal m : FractionalIdeal (𝓞 K)⁰ K) =
      ∏ v ∈ m.support, ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (-m v) := by
  rw [latticeIdeal, ClassField.Global.finiteDivisorFractionalIdeal_val, Finsupp.prod,
    Finsupp.support_neg, map_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Finsupp.neg_apply]

end LatticeIdeal

/-! ### Strong approximation -/

section Approximation

/-- **Strong approximation.** For finitely many places `v ∈ S`, centres `c v ∈ K_v` and levels
`m v`, some `x ∈ K` satisfies `x - c v ∈ π_v^{-m v} O_v` for `v ∈ S` and `x ∈ O_v` for `v ∉ S`. -/
theorem exists_approx (S : Finset (FinitePlace K)) (c : ∀ v : FinitePlace K, FiniteCompletion K v)
    (m : FinitePlace K → ℤ) :
    ∃ x : K, (∀ v ∈ S, algebraMap K (FiniteCompletion K v) x - c v ∈
        (topologicalData v).additiveLattice (m v)) ∧
      ∀ v ∉ S, algebraMap K (FiniteCompletion K v) x ∈ (topologicalData v).additiveLattice 0 := by
  classical
  set k : ℕ := ∑ v ∈ S, (m v).natAbs
  set δ : 𝓞 K := (∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)) ^ k with hδ
  have hδ0 : δ ≠ 0 := by
    refine pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
    exact_mod_cast Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  -- the valuation of `δ` is small at the places of `S`
  have hδv : ∀ v ∈ S, v.intValuation δ ≤ WithZero.exp (m v) := by
    intro v hv
    have h1 : v.intValuation ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ≤ WithZero.exp (-1) := by
      have := (intValuation_le_pow_iff_mem v ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) 1).mpr
        (by rw [pow_one]; exact Ideal.absNorm_mem v.asIdeal)
      simpa using this
    have h2 : v.intValuation (∏ w ∈ S, ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)) ≤
        WithZero.exp (-1) := by
      rw [← Finset.mul_prod_erase S _ hv, map_mul]
      calc _ ≤ WithZero.exp (-1) * 1 :=
            mul_le_mul' h1 (v.intValuation_le_one _)
        _ = _ := mul_one _
    have hk : (m v).natAbs ≤ k := Finset.single_le_sum (f := fun w => (m w).natAbs)
      (fun _ _ => Nat.zero_le _) hv
    calc v.intValuation δ = v.intValuation (∏ w ∈ S, ((Ideal.absNorm w.asIdeal : ℕ) : 𝓞 K)) ^ k :=
          map_pow _ _ _
      _ ≤ WithZero.exp (-1) ^ k := pow_le_pow_left₀ zero_le h2 k
      _ = WithZero.exp (-(k : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp
      _ ≤ WithZero.exp (m v) := by
          rw [WithZero.exp_le_exp]
          have : ((m v).natAbs : ℤ) ≤ k := by exact_mod_cast hk
          have := @Int.le_natAbs (-(m v))
          rw [Int.natAbs_neg] at this
          omega
  set δK : K := algebraMap (𝓞 K) K δ
  have hδK : δK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr hδ0
  have hδvK : ∀ v : FinitePlace K, Valued.v (algebraMap K (FiniteCompletion K v) δK) =
      v.intValuation δ := fun v => by
    rw [show algebraMap K (FiniteCompletion K v) δK = algebraMap (𝓞 K) (FiniteCompletion K v) δ from
      (IsScalarTower.algebraMap_apply _ _ _ _).symm]
    exact valued_algebraMap_integer v δ
  -- the finite adele `δ⁻¹ c` supported on `S`
  let a : FiniteAdeles K := ⟨fun v => if v ∈ S then
      (algebraMap K (FiniteCompletion K v) δK)⁻¹ * c v else 0,
    (S.eventually_cofinite_notMem).mono fun v hv => by simp [hv]⟩
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles a
  rw [mem_integralFiniteAdeles] at hx
  refine ⟨δK * x, fun v hv => ?_, fun v hv => ?_⟩
  · have hxv := hx v
    change (if v ∈ S then (algebraMap K (FiniteCompletion K v) δK)⁻¹ * c v else 0) -
      algebraMap K (FiniteCompletion K v) x ∈ v.adicCompletionIntegers K at hxv
    simp only [hv, ↓reduceIte] at hxv
    rw [mem_adicCompletionIntegers] at hxv
    have hne : algebraMap K (FiniteCompletion K v) δK ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap K (FiniteCompletion K v)).injective).mpr hδK
    have heq : algebraMap K (FiniteCompletion K v) (δK * x) - c v =
        -(algebraMap K (FiniteCompletion K v) δK *
          ((algebraMap K (FiniteCompletion K v) δK)⁻¹ * c v -
            algebraMap K (FiniteCompletion K v) x)) := by
      rw [map_mul]; field_simp; ring
    rw [mem_additiveLattice_iff_valued, heq, Valuation.map_neg, map_mul, hδvK]
    calc v.intValuation δ * Valued.v ((algebraMap K (FiniteCompletion K v) δK)⁻¹ * c v -
          algebraMap K (FiniteCompletion K v) x) ≤ v.intValuation δ * 1 :=
          mul_le_mul_right hxv _
      _ ≤ WithZero.exp (m v) := by rw [mul_one]; exact hδv v hv
  · have hxv := hx v
    change (if v ∈ S then (algebraMap K (FiniteCompletion K v) δK)⁻¹ * c v else 0) -
      algebraMap K (FiniteCompletion K v) x ∈ v.adicCompletionIntegers K at hxv
    simp only [hv, ↓reduceIte, zero_sub, neg_mem_iff] at hxv
    rw [mem_additiveLattice_zero_iff, map_mul]
    refine mul_mem ?_ hxv
    rw [mem_adicCompletionIntegers, hδvK]
    exact v.intValuation_le_one δ

end Approximation

/-! ### Self-dual Haar measures of valuation lattices -/

section LocalMeasure

variable {p : ℕ} [Fact p.Prime] {F : PadicField p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- A self-dual Haar measure for a character of conductor `n` gives the integers mass
`q ^ (-n / 2)`. -/
theorem selfDualHaar_integerRing (ψ : AdditiveCharacter)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel _
    μ.val.measure (LocalFactor.PadicAbelian.integerRing T) =
      ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(T.additiveConductor ψ : ℝ) / 2)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F.Carrier
  let := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have hnorm := (LocalFactors.padicFourierNormalization p F T ψ.toAddChar
    ψ.continuous_toFun ψ.nontrivial _ (T.isGreatest_fractionalIdeal_triviality ψ)).2.1
    μ.val.measure μ.val.isAddHaar
  have hmass := hnorm.mp (by
    intro f hlc hcomp x
    have h := (μ.property ⟨f, hlc, hcomp⟩).2 x
    change (∫ z, ψ.complex (z * x) *
      (∫ w, ψ.complex (w * z) * f w ∂μ.val.measure) ∂μ.val.measure) = f (-x) at h
    simpa only [Fourier.fourierIntegral_def, AddChar.inv_apply, neg_neg,
      Circle.smul_def, smul_eq_mul,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply] using h)
  simpa [LocalFactor.PadicAbelian.integerRing] using hmass

/-- The real mass of a valuation lattice under a self-dual Haar measure. -/
theorem selfDualHaar_additiveLattice (ψ : AdditiveCharacter)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ) (m : ℤ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel _
    (μ.val.measure (T.additiveLattice m : Set F.Carrier)).toReal =
      (T.residueCardinality : ℝ) ^ m *
        (T.residueCardinality : ℝ) ^ (-(T.additiveConductor ψ : ℝ) / 2) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  rw [((HarmonicAnalysis.padicLatticeHaar F T).1 μ.val m).2.2,
    ← LocalFactor.PadicAbelian.integerRing_eq_lattice_zero, selfDualHaar_integerRing,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- The real mass `μ(L(k))` of the valuation lattice `L(k) = π^{-k} O`. -/
def latticeMass (ψ : AdditiveCharacter) (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ) (k : ℤ) :
    ℝ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel _
  (μ.val.measure (T.additiveLattice k : Set F.Carrier)).toReal

theorem latticeMass_eq (ψ : AdditiveCharacter) (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
    (k : ℤ) :
    latticeMass T ψ μ k = (T.residueCardinality : ℝ) ^ k *
      (T.residueCardinality : ℝ) ^ (-(T.additiveConductor ψ : ℝ) / 2) :=
  selfDualHaar_additiveLattice T ψ μ k

/-- `μ(L(m)) μ(L(n - m)) = 1` for a self-dual Haar measure and `n` the additive conductor. -/
theorem measure_additiveLattice_mul_measure_dual (ψ : AdditiveCharacter)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ) (m : ℤ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel _
    (μ.val.measure (T.additiveLattice m : Set F.Carrier)).toReal *
      (μ.val.measure (T.additiveLattice (T.additiveConductor ψ - m) : Set F.Carrier)).toReal =
        1 := by
  rw [selfDualHaar_additiveLattice, selfDualHaar_additiveLattice]
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact LocalFactor.PadicAbelian.residueCardinality_pos' T
  set n := T.additiveConductor ψ
  set q : ℝ := ((T.residueCardinality : ℕ) : ℝ)
  have h1 : q ^ m * q ^ (n - m) = q ^ (n : ℝ) := by
    rw [← zpow_add₀ hq.ne', add_sub_cancel, Real.rpow_intCast]
  have h2 : q ^ (-(n : ℝ) / 2) * q ^ (-(n : ℝ) / 2) * q ^ (n : ℝ) = 1 := by
    rw [← Real.rpow_add hq, ← Real.rpow_add hq]
    norm_num
  calc q ^ m * q ^ (-(n : ℝ) / 2) * (q ^ (n - m) * q ^ (-(n : ℝ) / 2)) =
      q ^ (-(n : ℝ) / 2) * q ^ (-(n : ℝ) / 2) * (q ^ m * q ^ (n - m)) := by ring
    _ = 1 := by rw [h1, h2]

theorem latticeMass_mul_dual (ψ : AdditiveCharacter)
    (μ : LocalFactor.PadicAbelian.SelfDualHaar T ψ) (m : ℤ) :
    latticeMass T ψ μ m * latticeMass T ψ μ (T.additiveConductor ψ - m) = 1 :=
  measure_additiveLattice_mul_measure_dual T ψ μ m

end LocalMeasure

/-! ### Lattices in the mixed space -/

section Covolume

open scoped Classical

/-- A lattice spanned by a basis has the volume of the parallelepiped of the basis as covolume. -/
theorem covolume_eq_of_span_eq {ι : Type*} [Fintype ι] (b : Basis ι ℝ (mixedSpace K))
    (L : Submodule ℤ (mixedSpace K)) [DiscreteTopology L] [IsZLattice (E := mixedSpace K) ℝ L]
    (h : Submodule.span ℤ (Set.range b) = L) :
    ZLattice.covolume L = volume.real (parallelepiped b) := by
  subst h
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain b volume)]
  exact measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b volume)

/-- A sublattice has finite index: a fixed nonzero multiple of every vector of the larger lattice
lies in the smaller one. -/
theorem exists_nsmul_mem_of_le (L₁ L₂ : Submodule ℤ (mixedSpace K)) [DiscreteTopology L₁]
    [IsZLattice (E := mixedSpace K) ℝ L₁] [DiscreteTopology L₂]
    [IsZLattice (E := mixedSpace K) ℝ L₂] (h : L₁ ≤ L₂) :
    ∃ k : ℕ, k ≠ 0 ∧ ∀ w ∈ L₂, k • w ∈ L₁ := by
  let e := mixedEmbedding.euclidean.toMixed K
  let L₁' := ZLattice.comap ℝ L₁ e.toLinearMap
  let L₂' := ZLattice.comap ℝ L₂ e.toLinearMap
  have h' : L₁' ≤ L₂' := fun x hx => h hx
  have hrel := ZLattice.covolume_div_covolume_eq_relIndex' L₁' L₂' h'
  have hk : L₁'.toAddSubgroup.relIndex L₂'.toAddSubgroup ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hrel
    exact (div_pos (ZLattice.covolume_pos L₁' volume) (ZLattice.covolume_pos L₂' volume)).ne' hrel
  refine ⟨(L₁'.toAddSubgroup.relIndex L₂'.toAddSubgroup).factorial, Nat.factorial_ne_zero _,
    fun w hw => ?_⟩
  have hw' : e.symm w ∈ L₂' := by
    change e (e.symm w) ∈ L₂
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hw
  have hmem := (AddSubgroup.nsmul_mem_of_relIndex_ne_zero_of_dvd hk hw'
    fun j hj hle => Nat.dvd_factorial hj hle).1
  change e (_ • e.symm w) ∈ L₁ at hmem
  rwa [map_nsmul, ContinuousLinearEquiv.apply_symm_apply] at hmem

end Covolume

/-! ### The trace-dual of an ideal lattice -/

section Dual

open scoped Classical

variable (aR : {w : InfinitePlace K // IsReal w} → ℝ) (aC : {w : InfinitePlace K // IsComplex w} → ℂ)
  (ψf : ∀ v : FinitePlace K, @HarmonicAnalysis.UnitaryAdditiveCharacter
    (CompletionPadic.padicField v).Carrier _ (topologicalData v).topology)

/-- The additive product formula for the archimedean scales `aR, aC` and the finite local
characters `ψf`: for every `x ∈ K`, almost all `ψ_v(x)` equal `1` and
`𝐞(T(x)) ∏_v ψ_v(x) = 1`. -/
def AdditiveProductFormula : Prop :=
  ∀ x : K, ∃ S : Finset (FinitePlace K),
    (∀ v ∉ S, ψf v (algebraMap K (FiniteCompletion K v) x) = 1) ∧
      𝐞 (addTrace aR aC (mixedEmbedding K x)) *
        ∏ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) x) = 1

omit [NumberField K] in
theorem fourierChar_eq_one_iff (x : ℝ) : 𝐞 x = 1 ↔ ∃ n : ℤ, (n : ℝ) = x := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  refine exists_congr fun n => ⟨fun h => ?_, fun h => by rw [← h]; ring⟩
  have : (n : ℝ) * (2 * π) = x * (2 * π) := by rw [← h]; ring
  exact mul_right_cancel₀ hπ this

/-- Valuation lattices multiply: `L(a) L(b) ⊆ L(a + b)`. -/
theorem mul_mem_additiveLattice (v : FinitePlace K) {x y : FiniteCompletion K v} {a b : ℤ}
    (hx : x ∈ (topologicalData v).additiveLattice a)
    (hy : y ∈ (topologicalData v).additiveLattice b) :
    x * y ∈ (topologicalData v).additiveLattice (a + b) := by
  rw [mem_additiveLattice_iff_valued] at hx hy ⊢
  rw [map_mul, WithZero.exp_add]
  exact mul_le_mul' hx hy

variable {aR aC ψf}

/-- If `x ∈ K` lies in `π_v^{-n_v} O_v` at every finite place, `n_v` the additive conductor of
`ψ_v`, then `T(x)` is an integer. -/
theorem addTrace_mem_of_forall_mem (hprod : AdditiveProductFormula aR aC ψf) {x : K}
    (hx : ∀ v, algebraMap K (FiniteCompletion K v) x ∈
      (topologicalData v).additiveLattice ((topologicalData v).additiveConductor (ψf v))) :
    ∃ n : ℤ, (n : ℝ) = addTrace aR aC (mixedEmbedding K x) := by
  obtain ⟨S, -, hS⟩ := hprod x
  have h1 : ∀ v ∈ S, ψf v (algebraMap K (FiniteCompletion K v) x) = 1 := fun v _ =>
    ((topologicalData v).additiveConductor_spec (ψf v)).1 _ (hx v)
  rw [Finset.prod_eq_one h1, mul_one] at hS
  exact (fourierChar_eq_one_iff _).mp hS

/-- If `μ ∈ π_v^{-k_v} O_v` at every finite place and `m_v + k_v ≤ n_v`, `n_v` the additive
conductor, then `ι μ` lies in the trace-dual of the lattice of `latticeIdeal m`. -/
theorem mem_dualSubmodule_of_forall_mem (hprod : AdditiveProductFormula aR aC ψf)
    (m : FinitePlace K →₀ ℤ) (k : FinitePlace K → ℤ)
    (h : ∀ v, m v + k v ≤ (topologicalData v).additiveConductor (ψf v)) {μ : K}
    (hμ : ∀ v, algebraMap K (FiniteCompletion K v) μ ∈ (topologicalData v).additiveLattice (k v)) :
    mixedEmbedding K μ ∈ (tracePairing aR aC).flip.dualSubmodule
      (mixedEmbedding.idealLattice K (latticeIdeal m)) := by
  intro y hy
  obtain ⟨l, hl, rfl⟩ := (mixedEmbedding.mem_idealLattice K _).mp hy
  rw [LinearMap.BilinForm.flip_apply, tracePairing_apply, ← map_mul]
  obtain ⟨n, hn⟩ := addTrace_mem_of_forall_mem hprod (x := l * μ) fun v => by
    rw [map_mul]
    exact (topologicalData v).additiveLattice_mono (h v) (mul_mem_additiveLattice v
      ((mem_latticeIdeal_iff_forall_mem m l).mp hl v) (hμ v))
  exact Submodule.mem_one.mpr ⟨-n, by rw [← hn]; simp⟩

/-- **Dual lattice, easy inclusion.** If `m_v + m'_v ≤ n_v` at every place, the lattice of
`latticeIdeal m'` lies in the trace-dual of the lattice of `latticeIdeal m`. -/
theorem idealLattice_le_dualSubmodule (hprod : AdditiveProductFormula aR aC ψf)
    (m m' : FinitePlace K →₀ ℤ)
    (h : ∀ v, m v + m' v ≤ (topologicalData v).additiveConductor (ψf v)) :
    mixedEmbedding.idealLattice K (latticeIdeal m') ≤
      (tracePairing aR aC).flip.dualSubmodule
        (mixedEmbedding.idealLattice K (latticeIdeal m)) := by
  intro w hw
  obtain ⟨μ, hμ, rfl⟩ := (mixedEmbedding.mem_idealLattice K _).mp hw
  exact mem_dualSubmodule_of_forall_mem hprod m m' h ((mem_latticeIdeal_iff_forall_mem m' μ).mp hμ)

/-- The trace-dual of an ideal lattice is spanned by the dual basis of its lattice basis. -/
theorem dualSubmodule_idealLattice_eq_span (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    (tracePairing aR aC).flip.dualSubmodule (mixedEmbedding.idealLattice K I) =
      Submodule.span ℤ (Set.range ((tracePairing aR aC).flip.dualBasis
        (tracePairing_nondegenerate haR haC).flip (fractionalIdealLatticeBasis K I))) := by
  rw [← span_idealLatticeBasis, LinearMap.BilinForm.dualSubmodule_span_of_basis]

/-- Every vector of the trace-dual of an ideal lattice comes from `K`, as soon as the dual
contains some ideal lattice (which then has finite index in it). -/
theorem exists_eq_of_mem_dualSubmodule (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (m m' : FinitePlace K →₀ ℤ)
    (hle : mixedEmbedding.idealLattice K (latticeIdeal m') ≤
      (tracePairing aR aC).flip.dualSubmodule (mixedEmbedding.idealLattice K (latticeIdeal m)))
    {w : mixedSpace K}
    (hw : w ∈ (tracePairing aR aC).flip.dualSubmodule
      (mixedEmbedding.idealLattice K (latticeIdeal m))) :
    ∃ μ : K, mixedEmbedding K μ = w := by
  classical
  rw [dualSubmodule_idealLattice_eq_span haR haC] at hle hw
  obtain ⟨k, hk0, hk⟩ := exists_nsmul_mem_of_le _ _ hle
  obtain ⟨β, -, hβ⟩ := (mixedEmbedding.mem_idealLattice K _).mp (hk w hw)
  refine ⟨β / k, smul_right_injective (mixedSpace K) hk0 ?_⟩
  simp only
  rw [← hβ, ← map_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hk0)]

/-- **Dual lattice, hard inclusion (local form).** If `ι μ` lies in the trace-dual of the lattice
of `latticeIdeal m` and the conductors are nonnegative outside a finite set `S₀`, then
`μ ∈ π_v^{-(n_v - m_v)} O_v` at every finite place `v`. -/
theorem mem_additiveLattice_of_mem_dualSubmodule (hprod : AdditiveProductFormula aR aC ψf)
    (S₀ : Finset (FinitePlace K))
    (hS₀ : ∀ v ∉ S₀, 0 ≤ (topologicalData v).additiveConductor (ψf v))
    (m : FinitePlace K →₀ ℤ) {μ : K}
    (hμ : mixedEmbedding K μ ∈ (tracePairing aR aC).flip.dualSubmodule
      (mixedEmbedding.idealLattice K (latticeIdeal m))) (v₀ : FinitePlace K) :
    algebraMap K (FiniteCompletion K v₀) μ ∈ (topologicalData v₀).additiveLattice
      ((topologicalData v₀).additiveConductor (ψf v₀) - m v₀) := by
  classical
  by_contra hcon
  set n : FinitePlace K → ℤ := fun v => (topologicalData v).additiveConductor (ψf v) with hn_def
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hcon (by rw [map_zero]; exact zero_mem _)
  -- a local witness of the nontriviality at `v₀`
  obtain ⟨t, ht, hne⟩ : ∃ t ∈ (topologicalData v₀).additiveLattice (m v₀),
      ψf v₀ (t * algebraMap K (FiniteCompletion K v₀) μ) ≠ 1 := by
    by_contra h
    push Not at h
    exact hcon (((topologicalData v₀).forall_mul_eq_one_iff_mem_additiveLattice (ψf v₀) (m v₀)
      _).mp h)
  -- the valuation exponents of `μ`
  let e : FinitePlace K → ℤ := fun v =>
    WithZero.log (Valued.v (algebraMap K (FiniteCompletion K v) μ))
  have hμe : ∀ v, algebraMap K (FiniteCompletion K v) μ ∈
      (topologicalData v).additiveLattice (e v) := fun v => by
    rw [mem_additiveLattice_iff_valued, WithZero.exp_log]
    exact (Valuation.ne_zero_iff _).mpr ((map_ne_zero _).mpr hμ0)
  -- the finite set of special places
  set S : Finset (FinitePlace K) := insert v₀ (S₀ ∪ m.support ∪
    (finite_setOf_not_mem_additiveLattice_zero μ).toFinset) with hS_def
  obtain ⟨l, hlS, hlout⟩ := exists_approx S (Pi.single v₀ (t : FiniteCompletion K v₀))
    (fun v => min (m v) (n v - e v))
  have hl_mem : ∀ v, algebraMap K (FiniteCompletion K v) l ∈
      (topologicalData v).additiveLattice (m v) := by
    intro v
    by_cases hvS : v ∈ S
    · have h1 := (topologicalData v).additiveLattice_mono (min_le_left _ _) (hlS v hvS)
      by_cases hv : v = v₀
      · subst hv
        rw [Pi.single_eq_same] at h1
        simpa using add_mem h1 ht
      · rwa [Pi.single_eq_of_ne hv, sub_zero] at h1
    · have hm : m v = 0 := by
        by_contra hm
        exact hvS (by simp [hS_def, hm])
      rw [hm]
      exact hlout v hvS
  have hl_triv : ∀ v ≠ v₀, ψf v (algebraMap K (FiniteCompletion K v) (l * μ)) = 1 := by
    intro v hv
    apply ((topologicalData v).additiveConductor_spec (ψf v)).1
    rw [map_mul]
    by_cases hvS : v ∈ S
    · have h1 := (topologicalData v).additiveLattice_mono (min_le_right _ _) (hlS v hvS)
      rw [Pi.single_eq_of_ne hv, sub_zero] at h1
      simpa using mul_mem_additiveLattice v h1 (hμe v)
    · have hvS₀ : v ∉ S₀ := fun h => hvS (by simp [hS_def, h])
      have hvμ : algebraMap K (FiniteCompletion K v) μ ∈ (topologicalData v).additiveLattice 0 := by
        by_contra h
        exact hvS (by simp [hS_def, h])
      exact (topologicalData v).additiveLattice_mono (hS₀ v hvS₀)
        (by simpa using mul_mem_additiveLattice v (hlout v hvS) hvμ)
  have hl_v₀ : ψf v₀ (algebraMap K (FiniteCompletion K v₀) (l * μ)) =
      ψf v₀ (t * algebraMap K (FiniteCompletion K v₀) μ) := by
    have h1 := (topologicalData v₀).additiveLattice_mono (min_le_right _ _)
      (hlS v₀ (Finset.mem_insert_self _ _))
    rw [Pi.single_eq_same] at h1
    have h2 : ψf v₀ ((algebraMap K (FiniteCompletion K v₀) l - t) *
        algebraMap K (FiniteCompletion K v₀) μ) = 1 :=
      ((topologicalData v₀).additiveConductor_spec (ψf v₀)).1 _
        (by simpa using mul_mem_additiveLattice v₀ h1 (hμe v₀))
    have h3 : algebraMap K (FiniteCompletion K v₀) (l * μ) =
        t * algebraMap K (FiniteCompletion K v₀) μ +
          (algebraMap K (FiniteCompletion K v₀) l - t) * algebraMap K (FiniteCompletion K v₀) μ := by
      rw [map_mul]; ring
    rw [h3, AddChar.map_add_eq_mul (ψf v₀).toAddChar]
    change _ * ψf v₀ _ = _
    rw [h2, mul_one]
  -- the trace of `l μ` is an integer
  have hT := hμ (mixedEmbedding K l) ((mixedEmbedding.mem_idealLattice K _).mpr
    ⟨l, (mem_latticeIdeal_iff_forall_mem m l).mpr hl_mem, rfl⟩)
  rw [LinearMap.BilinForm.flip_apply, tracePairing_apply, ← map_mul, Submodule.mem_one] at hT
  obtain ⟨k, hk⟩ := hT
  obtain ⟨S', hS'out, hS'⟩ := hprod (l * μ)
  have hE : 𝐞 (addTrace aR aC (mixedEmbedding K (l * μ))) = 1 :=
    (fourierChar_eq_one_iff _).mpr ⟨-k, by
      simp only [algebraMap_int_eq, eq_intCast] at hk
      push_cast
      linarith⟩
  rw [hE, one_mul] at hS'
  by_cases hv₀ : v₀ ∈ S'
  · rw [← Finset.mul_prod_erase S' _ hv₀,
      Finset.prod_eq_one fun v hv => hl_triv v (Finset.ne_of_mem_erase hv), mul_one,
      hl_v₀] at hS'
    exact hne hS'
  · exact hne (hl_v₀ ▸ hS'out v₀ hv₀)

/-- **Finiteness of the conductor.** If the additive conductors are nonnegative outside a finite
set `S₀`, they vanish outside a finite set. The trace-dual of the lattice of integers is finitely
generated by elements of `K`; at a place where all generators are integral and `n_v ≥ 1`, strong
approximation produces an element of the dual which is not integral at `v`. -/
theorem finite_setOf_additiveConductor_ne_zero (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf) (S₀ : Finset (FinitePlace K))
    (hS₀ : ∀ v ∉ S₀, 0 ≤ (topologicalData v).additiveConductor (ψf v)) :
    {v : FinitePlace K | (topologicalData v).additiveConductor (ψf v) ≠ 0}.Finite := by
  set n : FinitePlace K → ℤ := fun v => (topologicalData v).additiveConductor (ψf v) with hn_def
  -- an ideal lattice inside the dual of the lattice of integers
  let m'' : FinitePlace K →₀ ℤ := Finsupp.onFinset S₀
    (fun v => if v ∈ S₀ then min (n v) 0 else 0) (fun v hv => by
      by_contra h
      exact hv (by simp [h]))
  have hm'' : ∀ v, (0 : FinitePlace K →₀ ℤ) v + m'' v ≤ n v := by
    intro v
    simp only [Finsupp.coe_zero, Pi.zero_apply, zero_add, m'', Finsupp.onFinset_apply]
    split_ifs with hv
    · exact min_le_left _ _
    · exact hS₀ v hv
  have hle := idealLattice_le_dualSubmodule hprod 0 m'' hm''
  set b' := (tracePairing aR aC).flip.dualBasis (tracePairing_nondegenerate haR haC).flip
    (fractionalIdealLatticeBasis K (latticeIdeal (0 : FinitePlace K →₀ ℤ))) with hb'
  have hspan := dualSubmodule_idealLattice_eq_span haR haC
    (latticeIdeal (0 : FinitePlace K →₀ ℤ))
  -- the dual basis vectors come from `K`
  have hgen : ∀ j, ∃ μ : K, mixedEmbedding K μ = b' j := fun j =>
    exists_eq_of_mem_dualSubmodule haR haC 0 m'' hle
      (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩)
  choose μ hμ using hgen
  -- the finite set of places where some generator is not integral
  have hB : (⋃ j, {v : FinitePlace K | algebraMap K (FiniteCompletion K v) (μ j) ∉
      (topologicalData v).additiveLattice 0}).Finite :=
    Set.finite_iUnion fun j => finite_setOf_not_mem_additiveLattice_zero (μ j)
  refine (hB.union S₀.finite_toSet).subset fun v hv => ?_
  by_contra hvB
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, not_or, not_exists, not_not,
    Finset.mem_coe] at hvB
  obtain ⟨hμv, hvS₀⟩ := hvB
  have hnv : 1 ≤ n v := by
    have h1 : 0 ≤ n v := hS₀ v hvS₀
    have h2 : n v ≠ 0 := hv
    omega
  -- an element of `K` close to `π_v⁻¹` at `v` and in `L(n_w)` at every other place
  set π' : FiniteCompletion K v := (topologicalData v).uniformizer⁻¹ with hπ'
  have hπ1 : π' ∈ (topologicalData v).additiveLattice 1 := by
    rw [PadicField.TopologicalData.mem_additiveLattice, hπ', map_inv₀,
      PadicField.TopologicalData.discreteValuation_uniformizer, WithZero.inv_exp, neg_neg]
  obtain ⟨l, hlS, hlout⟩ := exists_approx (insert v S₀) (Pi.single v π')
    (fun w => if w = v then 0 else min (n w) 0)
  have hlv0 : algebraMap K (FiniteCompletion K v) l - π' ∈ (topologicalData v).additiveLattice 0 := by
    have h1 := hlS v (Finset.mem_insert_self _ _)
    simp only [Pi.single_eq_same, ↓reduceIte] at h1
    exact h1
  have hl_mem : ∀ w, algebraMap K (FiniteCompletion K w) l ∈
      (topologicalData w).additiveLattice (n w) := by
    intro w
    rcases eq_or_ne w v with rfl | hw
    · have h1 := add_mem ((topologicalData w).additiveLattice_mono zero_le_one hlv0) hπ1
      rw [sub_add_cancel] at h1
      exact (topologicalData w).additiveLattice_mono hnv h1
    · by_cases hwS : w ∈ insert v S₀
      · have h1 := hlS w hwS
        simp only [Pi.single_eq_of_ne hw, sub_zero, hw, ↓reduceIte] at h1
        exact (topologicalData w).additiveLattice_mono (min_le_left _ _) h1
      · have hwS₀ : w ∉ S₀ := fun h => hwS (Finset.mem_insert_of_mem h)
        exact (topologicalData w).additiveLattice_mono (hS₀ w hwS₀) (hlout w hwS)
  -- so `ι l` lies in the dual lattice, hence is an integral combination of the generators
  have hlD := mem_dualSubmodule_of_forall_mem hprod 0 n (fun w => by simp [n]) hl_mem
  rw [hspan] at hlD
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hlD
  have hl_eq : l = ∑ j, c j • μ j := by
    apply mixedEmbedding_injective K
    rw [← hc, map_sum]
    simp_rw [map_zsmul, hμ, hb']
  have hlv : algebraMap K (FiniteCompletion K v) l ∈ (topologicalData v).additiveLattice 0 := by
    rw [hl_eq, map_sum]
    exact sum_mem fun j _ => by rw [map_zsmul]; exact zsmul_mem (hμv j) _
  have hπ0 : π' ∈ (topologicalData v).additiveLattice 0 := by
    simpa using sub_mem hlv hlv0
  exact HeckeFunctionalEquation.inverse_uniformizer_not_mem_integers (topologicalData v)
    (((topologicalData v).mem_additiveLattice_zero π').mp hπ0)

/-- **The trace-dual of an ideal lattice.** If the additive conductors form the finitely
supported vector `n`, the trace-dual of the lattice of `latticeIdeal m` is the lattice of
`latticeIdeal (n - m)`. -/
theorem dualSubmodule_idealLattice (haR : ∀ v, aR v ≠ 0) (haC : ∀ v, aC v ≠ 0)
    (hprod : AdditiveProductFormula aR aC ψf) (n : FinitePlace K →₀ ℤ)
    (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v) (m : FinitePlace K →₀ ℤ) :
    (tracePairing aR aC).flip.dualSubmodule (mixedEmbedding.idealLattice K (latticeIdeal m)) =
      mixedEmbedding.idealLattice K (latticeIdeal (n - m)) := by
  have hle := idealLattice_le_dualSubmodule hprod m (n - m) fun v => by simp [hn v]
  refine le_antisymm (fun w hw => ?_) hle
  obtain ⟨μ, rfl⟩ := exists_eq_of_mem_dualSubmodule haR haC m (n - m) hle hw
  refine (mixedEmbedding.mem_idealLattice K _).mpr
    ⟨μ, (mem_latticeIdeal_iff_forall_mem _ μ).mpr fun v => ?_, rfl⟩
  have h := mem_additiveLattice_of_mem_dualSubmodule hprod n.support
    (fun v hv => by rw [hn v, Finsupp.notMem_support_iff.mp hv]) m hw v
  rw [Finsupp.sub_apply]
  rwa [hn v] at h

end Dual

/-! ### Tamagawa normalization -/

section Tamagawa

open scoped Classical

variable {aR : {w : InfinitePlace K // IsReal w} → ℝ} {aC : {w : InfinitePlace K // IsComplex w} → ℂ}
  {ψf : ∀ v : FinitePlace K, @HarmonicAnalysis.UnitaryAdditiveCharacter
    (CompletionPadic.padicField v).Carrier _ (topologicalData v).topology}

/-- **Tamagawa normalization.** Let the additive conductors form the finitely supported vector
`n`, and let `S` contain the supports of `m` and `n`. Then
`κ covol(Λ_m) ∏_{v ∈ S} μ_v(L_v(m_v)) = 1`, where `Λ_m` is the lattice of `latticeIdeal m`,
`κ = ∏ √|aR v| ∏ 2 |aC v|` and `μ_v` are self-dual Haar measures. -/
theorem mixedGaussianConst_mul_covolume_mul_prod_latticeMass (haR : ∀ v, aR v ≠ 0)
    (haC : ∀ v, aC v ≠ 0) (hprod : AdditiveProductFormula aR aC ψf) (n : FinitePlace K →₀ ℤ)
    (hn : ∀ v, (topologicalData v).additiveConductor (ψf v) = n v)
    (μ : ∀ v : FinitePlace K, LocalFactor.PadicAbelian.SelfDualHaar (topologicalData v) (ψf v))
    (m : FinitePlace K →₀ ℤ) (S : Finset (FinitePlace K)) (hmS : m.support ⊆ S)
    (hnS : n.support ⊆ S) :
    mixedGaussianConst aR aC * ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal m)) *
      ∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) (m v) = 1 := by
  set κ := mixedGaussianConst aR aC
  set q : FinitePlace K → ℝ := fun v => ((topologicalData v).residueCardinality : ℝ) with hq_def
  have hq : ∀ v, 0 < q v := fun v => LocalFactor.PadicAbelian.residueCardinality_pos' _
  have hmass : ∀ v k, latticeMass (topologicalData v) (ψf v) (μ v) k =
      q v ^ k * q v ^ (-(n v : ℝ) / 2) := fun v k => by
    rw [latticeMass_eq, hn v]
  -- covolumes of ideal lattices
  have hcov : ∀ m' : FinitePlace K →₀ ℤ,
      ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal m')) =
        (∏ v ∈ m'.support, q v ^ (-m' v)) *
          ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal 0)) := by
    intro m'
    rw [mixedEmbedding.covolume_idealLattice, mixedEmbedding.covolume_idealLattice,
      absNorm_latticeIdeal, absNorm_latticeIdeal, Finsupp.support_zero, Finset.prod_empty]
    simp only [hq_def, HeckeEulerProduct.residueCardinality_eq, Rat.cast_prod, Rat.cast_zpow,
      Rat.cast_natCast, Rat.cast_one]
    ring
  -- the normalized product does not depend on `m`
  have hC : ∀ m' : FinitePlace K →₀ ℤ, m'.support ⊆ S →
      κ * ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal m')) *
        ∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) (m' v) =
      κ * ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal 0)) *
        ∏ v ∈ S, q v ^ (-(n v : ℝ) / 2) := by
    intro m' hm'
    rw [hcov, Finset.prod_subset hm' (fun v _ hv => by
      rw [Finsupp.notMem_support_iff.mp hv, neg_zero, zpow_zero])]
    simp_rw [hmass]
    rw [Finset.prod_mul_distrib]
    have h1 : (∏ v ∈ S, q v ^ (-m' v)) * ∏ v ∈ S, q v ^ m' v = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun v _ => by
        rw [← zpow_add₀ (hq v).ne', neg_add_cancel, zpow_zero]
    linear_combination (κ * ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal 0)) *
      ∏ v ∈ S, q v ^ (-(n v : ℝ) / 2)) * h1
  set X := κ * ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal 0)) *
    ∏ v ∈ S, q v ^ (-(n v : ℝ) / 2) with hX
  rw [hC m hmS]
  -- covolume duality between `Λ_0` and `Λ_n`
  set b := fractionalIdealLatticeBasis K (latticeIdeal (0 : FinitePlace K →₀ ℤ))
  set b' := (tracePairing aR aC).flip.dualBasis (tracePairing_nondegenerate haR haC).flip b
  have hcov0 : ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal 0)) =
      volume.real (parallelepiped b) :=
    covolume_eq_of_span_eq b _ (span_idealLatticeBasis K _)
  have hcovn : ZLattice.covolume (mixedEmbedding.idealLattice K (latticeIdeal n)) =
      volume.real (parallelepiped b') := by
    refine covolume_eq_of_span_eq b' _ ?_
    rw [← dualSubmodule_idealLattice_eq_span haR haC,
      dualSubmodule_idealLattice haR haC hprod n hn 0, sub_zero]
  have hD := measureReal_parallelepiped_mul_dualBasis haR haC b
  have hloc : ∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) 0 *
      latticeMass (topologicalData v) (ψf v) (μ v) (n v) = 1 :=
    Finset.prod_eq_one fun v _ => by
      have h := latticeMass_mul_dual (topologicalData v) (ψf v) (μ v) 0
      rwa [sub_zero, hn v] at h
  have h0 := hC 0 (by simp)
  have hnn := hC n hnS
  simp only [Finsupp.coe_zero, Pi.zero_apply] at h0
  have hXX : X * X = 1 := by
    rw [show X * X = _ * _ from congrArg₂ (· * ·) h0.symm hnn.symm, hcov0, hcovn]
    calc κ * volume.real (parallelepiped b) *
          (∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) 0) *
        (κ * volume.real (parallelepiped b') *
          ∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) (n v)) =
        (volume.real (parallelepiped b) * volume.real (parallelepiped b') * κ ^ 2) *
          ∏ v ∈ S, latticeMass (topologicalData v) (ψf v) (μ v) 0 *
            latticeMass (topologicalData v) (ψf v) (μ v) (n v) := by
          rw [Finset.prod_mul_distrib]; ring
      _ = 1 := by rw [hloc, mul_one]; exact hD
  have hX0 : 0 ≤ X :=
    mul_nonneg (mul_nonneg (mixedGaussianConst_pos haR haC).le
      (ZLattice.covolume_pos _ volume).le)
      (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (hq v).le _)
  rcases mul_self_eq_one_iff.mp hXX with h | h
  · exact h
  · linarith

end Tamagawa

end Langlands.Global.Hecke
