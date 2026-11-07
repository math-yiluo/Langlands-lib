import Langlands.LocalFactor.Abelian.GaussDual
import Langlands.LocalFactor.Abelian.ZetaMeromorphic
import Langlands.HarmonicAnalysis.PadicLatticeHaarProof

/-!
# Lattice-coset zeta integrals

Indicators of lattice cosets are test functions. Their zeta integrals are
computed in the half-plane of convergence: the unit average of `χ` is the unit
mass or zero, a lattice gives a geometric series over order shells, and a coset
avoiding zero lies in one shell, where `χ` is constant or averages to zero.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.LocalFactor.PadicAbelian

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)
local notation "TestFunction" => @HarmonicAnalysis.SchwartzBruhat F.Carrier T.topology

theorem coset_zero (m : ℤ) :
    {z : F.Carrier | z - 0 ∈ T.additiveLattice m} = (T.additiveLattice m : Set F.Carrier) := by
  ext z
  simp

theorem coset_eq_of_mem (m : ℤ) {b : F.Carrier} (hb : b ∈ T.additiveLattice m) :
    {z : F.Carrier | z - b ∈ T.additiveLattice m} = (T.additiveLattice m : Set F.Carrier) := by
  ext z
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · intro h
    simpa using add_mem h hb
  · intro h
    exact sub_mem h hb

/-- The indicator of a lattice coset is locally constant. -/
theorem cosetIndicator_isLocallyConstant (m : ℤ) (b : F.Carrier) :
    letI := T.topology
    IsLocallyConstant
      ({z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (T.additiveLattice m : Set F.Carrier), ?_, ?_, ?_⟩
  · exact (T.isOpen_additiveLattice _).preimage (continuous_id.sub continuous_const)
  · simp only [Set.mem_preimage, sub_self, SetLike.mem_coe]
    exact (T.additiveLattice _).zero_mem
  · intro y hy
    have hy' : y - x ∈ T.additiveLattice m := hy
    have hiff : y - b ∈ T.additiveLattice m ↔ x - b ∈ T.additiveLattice m := by
      constructor
      · intro h
        have := sub_mem h hy'
        rwa [show y - b - (y - x) = x - b by ring] at this
      · intro h
        have := add_mem h hy'
        rwa [show x - b + (y - x) = y - b by ring] at this
    by_cases hx : x - b ∈ T.additiveLattice m
    · rw [Set.indicator_of_mem
          (show y ∈ {z : F.Carrier | z - b ∈ T.additiveLattice m} from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ {z : F.Carrier | z - b ∈ T.additiveLattice m} from hx)]
    · rw [Set.indicator_of_notMem
          (show y ∉ {z : F.Carrier | z - b ∈ T.additiveLattice m} from fun h => hx (hiff.mp h)),
        Set.indicator_of_notMem (show x ∉ {z : F.Carrier | z - b ∈ T.additiveLattice m} from hx)]

/-- The indicator of a lattice coset has compact support. -/
theorem cosetIndicator_hasCompactSupport (m : ℤ) (b : F.Carrier) :
    letI := T.topology
    HasCompactSupport
      ({z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply HasCompactSupport.intro ((T.isCompact_additiveLattice m).image
    (f := fun t => t + b) (continuous_id.add continuous_const))
  intro x hx
  apply Set.indicator_of_notMem
  intro hC
  exact hx ⟨x - b, hC, sub_add_cancel x b⟩

/-- The indicator of the lattice coset `b + π^(-m) O` as a test function. -/
def cosetTest (m : ℤ) (b : F.Carrier) : TestFunction :=
  letI := T.topology
  ⟨{z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ)),
    cosetIndicator_isLocallyConstant T m b, cosetIndicator_hasCompactSupport T m b⟩

theorem cosetTest_coe (m : ℤ) (b : F.Carrier) :
    (cosetTest T m b : F.Carrier → ℂ) =
      {z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ)) := rfl

/-- The average of a quasicharacter over the integral units is the unit mass when
it is unramified and zero when it is ramified. -/
theorem setIntegral_integralUnits_characterExtension (μ : LocalHaar) (χ : Character) {a : ℕ}
    (hχ : ConductorAt T χ a) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure =
      if a = 0 then ((μ.measure (integralUnits T)).toReal : ℂ) else 0 := by
  let := T.topology
  let := borel F.Carrier
  split_ifs with ha
  · subst ha
    have hc : ∀ x ∈ integralUnits T, characterExtension T χ x = 1 := by
      intro x hx
      have hl : unitLevel T 0 (Units.mk0 x hx.1) := by simpa [unitLevel] using hx.2
      simp only [characterExtension, hx.1, dite_false, hχ.1 _ hl, Units.val_one]
    have hUm : MeasurableSet (integralUnits T) := (orderShell_compact_measurable T 0).2
    rw [setIntegral_congr_fun hUm hc, setIntegral_const,
      measureReal_def, Complex.real_smul, mul_one]
  · have h := gauss_shell_integral_eq_zero_of_lt T μ χ⁻¹ (conductorAt_inv T χ a hχ) ha
      (1 : AddChar F.Carrier Circle) 0 (fun _ _ => AddChar.one_apply _) 0 (by omega)
    rw [integralUnits_eq_gaussShell_zero, ← h]
    apply setIntegral_congr_fun (gaussShell_measurableSet T 0)
    intro x _
    simp [gaussIntegrand_zero_apply, characterExtension_inv]

/-- The zeta integral of the lattice `π^(-M) O` in the half-plane of convergence:
the geometric series over the shells of order at least `-M`. -/
theorem zeta_additiveLattice (π : F.Carrierˣ) (hπ : T.ord (π : F.Carrier) = 1)
    (χ : Character) (μ : LocalHaar) {s : ℂ} (hs : ConvergesAt T π χ s) (M : ℤ) :
    letI := T.topology
    letI := borel F.Carrier
    zeta T μ.measure ((T.additiveLattice M : Set F.Carrier).indicator (fun _ => (1 : ℂ))) χ s =
      (1 - (χ π : ℂ) * spectralVariable T s)⁻¹ *
        ((χ π : ℂ) * spectralVariable T s) ^ (-M) *
          ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  set f := (T.additiveLattice M : Set F.Carrier).indicator (fun _ => (1 : ℂ)) with hf
  set X := (χ π : ℂ) * spectralVariable T s with hX
  set A := ∫ x in integralUnits T, characterExtension T χ x ∂μ.measure with hA
  have hXn : ‖X‖ < 1 := (convergesAt_iff_norm_lt_one T π χ s).mp hs
  have hX0 : X ≠ 0 := mul_ne_zero (χ π).ne_zero (spectralVariable_ne_zero T s)
  have hint : Integrable (zetaIntegrand T f χ s) μ.measure := by
    have h := zeta_integrable T π hπ χ μ (cosetTest T M 0) s hs
    rwa [cosetTest_coe, coset_zero] at h
  set S : ℕ → Set F.Carrier := fun i => orderShell T ((i : ℤ) - M) with hS
  have hsupp : ∀ x ∉ ⋃ i, S i, zetaIntegrand T f χ s x = 0 := by
    intro x hx
    by_cases h0 : x = 0
    · simp [zetaIntegrand, h0]
    by_cases hL : x ∈ (T.additiveLattice M : Set F.Carrier)
    · exfalso
      apply hx
      have hord := (gauss_valuation_le_exp_iff T h0 M).mp hL
      have htn := Int.toNat_of_nonneg (show 0 ≤ T.ord x + M by omega)
      refine Set.mem_iUnion.mpr ⟨(T.ord x + M).toNat, h0, ?_⟩
      omega
    · simp [zetaIntegrand, h0, hf, Set.indicator_of_notMem hL]
  have hint_eq : zeta T μ.measure f χ s =
      ∫ x in ⋃ i, S i, zetaIntegrand T f χ s x ∂μ.measure :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have hmeas : ∀ i, MeasurableSet (S i) := fun i => (orderShell_compact_measurable T _).2
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hx hy => hij ?_
    have := hx.2.symm.trans hy.2
    omega
  have hsum := hasSum_integral_iUnion hmeas hdisj hint.integrableOn
  have hterm : ∀ i : ℕ, ∫ x in S i, zetaIntegrand T f χ s x ∂μ.measure =
      X ^ (-M) * X ^ i * A := by
    intro i
    rw [hS, setIntegral_zeta_orderShell T π hπ χ μ f s]
    have hU : ∫ x in integralUnits T,
        f (((π ^ ((i : ℤ) - M) : F.Carrierˣ) : F.Carrier) * x) * characterExtension T χ x
          ∂μ.measure = A := by
      apply setIntegral_congr_fun (orderShell_compact_measurable T 0).2
      intro x hx
      have hm := (mul_uniformizer_mem_orderShell_iff T π hπ ((i : ℤ) - M) x).mpr hx
      have hmem : ((π ^ ((i : ℤ) - M) : F.Carrierˣ) : F.Carrier) * x ∈
          (T.additiveLattice M : Set F.Carrier) := by
        rw [SetLike.mem_coe, T.mem_additiveLattice, gauss_valuation_le_exp_iff T hm.1, hm.2]
        omega
      simp only [hf, Set.indicator_of_mem hmem, one_mul]
    rw [hU, show ((i : ℤ) - M) = (i : ℤ) + -M by ring, zpow_add₀ hX0, zpow_natCast]
    ring
  have hsum' : HasSum (fun i : ℕ => X ^ (-M) * X ^ i * A)
      (∫ x in ⋃ i, S i, zetaIntegrand T f χ s x ∂μ.measure) := by
    simpa only [hterm] using hsum
  have hgeo : HasSum (fun i : ℕ => X ^ (-M) * X ^ i * A) (X ^ (-M) * (1 - X)⁻¹ * A) :=
    ((hasSum_geometric_of_norm_lt_one hXn).mul_left (X ^ (-M))).mul_right A
  rw [hint_eq, hsum'.unique hgeo]
  ring

/-- Change of variables `x ↦ b x` on an arbitrary set. -/
theorem setIntegral_preimage_mul_unit (μ : LocalHaar) (b : F.Carrierˣ) (S : Set F.Carrier)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : F.Carrier → E) :
    letI := T.topology
    letI := borel F.Carrier
    ∫ x in (fun x => (b : F.Carrier) * x) ⁻¹' S, g ((b : F.Carrier) * x) ∂μ.measure =
      ((T.normalizedAbs (b : F.Carrier))⁻¹ : ℝ) • ∫ x in S, g x ∂μ.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have hmap := HarmonicAnalysis.padicScalarHaarScaling F T μ.measure b
  have hsub := (Homeomorph.mulLeft₀ (b : F.Carrier) b.ne_zero).measurableEmbedding.setIntegral_map
    (μ := μ.measure) g S
  calc
    _ = ∫ y in S, g y ∂μ.measure.map (fun x => (b : F.Carrier) * x) := hsub.symm
    _ = ((T.normalizedAbsUnits b : NNReal)⁻¹) • ∫ y in S, g y ∂μ.measure := by
        rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
    _ = _ := by rw [NNReal.smul_def, NNReal.coe_inv, T.normalizedAbsUnits_coe]

theorem normalizedAbs_of_mem_principalUnits {k : ℕ} {u : F.Carrierˣ}
    (hu : u ∈ T.principalUnits k) : T.normalizedAbs (u : F.Carrier) = 1 := by
  have hv : T.discreteValuation (u : F.Carrier) = 1 := hu.1
  rw [T.normalizedAbs_of_ne_zero u.ne_zero]
  simp [PadicField.TopologicalData.ord, hv]

/-- A point of a coset of `π^(-m) O` avoiding the lattice is `b` times a principal unit
of level `-m - ord b`. -/
theorem exists_principalUnit_of_mem_coset (m : ℤ) (b : F.Carrierˣ)
    (hb : (b : F.Carrier) ∉ T.additiveLattice m) {z : F.Carrier}
    (hz : z - b ∈ T.additiveLattice m) :
    ∃ w : F.Carrierˣ, w ∈ T.principalUnits (-m - T.ord (b : F.Carrier)).toNat ∧
      z = (b : F.Carrier) * w := by
  have hb0 := b.ne_zero
  have hord : T.ord (b : F.Carrier) < -m := by
    by_contra h
    exact hb ((gauss_valuation_le_exp_iff T hb0 m).mpr (by omega))
  have hjn : (((-m - T.ord (b : F.Carrier)).toNat : ℕ) : ℤ) = -m - T.ord (b : F.Carrier) :=
    Int.toNat_of_nonneg (by omega)
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hb
    simpa using neg_mem hz
  refine ⟨Units.mk0 (z / b) (div_ne_zero hz0 hb0), ?_, ?_⟩
  · rw [T.mem_principalUnits, Units.val_mk0]
    by_cases hzb : z - b = 0
    · have h1 : z / b = 1 := by rw [sub_eq_zero.mp hzb, div_self hb0]
      simp [h1]
    · have hw1 : z / b - 1 = (z - b) / b := by field_simp
      have hw10 : z / b - 1 ≠ 0 := by rw [hw1]; exact div_ne_zero hzb hb0
      have hord1 : T.ord (z / b - 1) = T.ord (z - b) - T.ord (b : F.Carrier) := by
        rw [hw1, div_eq_mul_inv, T.ord_mul hzb (inv_ne_zero hb0), T.ord_inv]
        ring
      have hzb' := (gauss_valuation_le_exp_iff T hzb m).mp hz
      have hlt : T.discreteValuation (z / b - 1) < T.discreteValuation (1 : F.Carrier) := by
        rw [map_one, gauss_valuation_eq_exp_neg_ord T hw10, ← WithZero.exp_zero,
          WithZero.exp_lt_exp]
        omega
      refine ⟨?_, ?_⟩
      · calc T.discreteValuation (z / b) = T.discreteValuation (1 + (z / b - 1)) := by ring_nf
          _ = T.discreteValuation (1 : F.Carrier) :=
            T.discreteValuation.map_add_eq_of_lt_left hlt
          _ = 1 := map_one _
      · rw [gauss_valuation_le_exp_iff T hw10]
        omega
  · rw [Units.val_mk0]
    field_simp

/-- The zeta integral of a lattice coset `b + π^(-m) O` avoiding the lattice. The coset
lies in the shell of `b`; the integral is `χ(b) |b|^(s-1) μ(π^(-m) O)` when the
character is trivial on the principal units of level `-m - ord b`, and zero otherwise. -/
theorem zeta_coset_of_not_mem (χ : Character) {a : ℕ} (hχ : ConductorAt T χ a)
    (μ : LocalHaar) (s : ℂ) (m : ℤ) (b : F.Carrierˣ)
    (hb : (b : F.Carrier) ∉ T.additiveLattice m) :
    letI := T.topology
    letI := borel F.Carrier
    zeta T μ.measure
        ({z : F.Carrier | z - b ∈ T.additiveLattice m}.indicator (fun _ => (1 : ℂ))) χ s =
      if (a : ℤ) ≤ -m - T.ord (b : F.Carrier) then
        (χ b : ℂ) * Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) *
          ((μ.measure (T.additiveLattice m : Set F.Carrier)).toReal : ℂ)
      else 0 := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  set C := {z : F.Carrier | z - b ∈ T.additiveLattice m} with hCdef
  set g : F.Carrier → ℂ := fun x => characterExtension T χ x *
    Complex.exp ((s - 1) * (Real.log (T.normalizedAbs x) : ℂ)) with hg
  have hb0 := b.ne_zero
  have hord : T.ord (b : F.Carrier) < -m := by
    by_contra h
    exact hb ((gauss_valuation_le_exp_iff T hb0 m).mpr (by omega))
  have hjn : (((-m - T.ord (b : F.Carrier)).toNat : ℕ) : ℤ) = -m - T.ord (b : F.Carrier) :=
    Int.toNat_of_nonneg (by omega)
  have h0C : (0 : F.Carrier) ∉ C := by
    intro h
    apply hb
    have h' : (0 : F.Carrier) - b ∈ T.additiveLattice m := h
    simpa using neg_mem h'
  have hCm : MeasurableSet C :=
    ((T.isOpen_additiveLattice m).preimage (continuous_id.sub continuous_const)).measurableSet
  have hpt : zetaIntegrand T (C.indicator (fun _ => (1 : ℂ))) χ s = C.indicator g := by
    funext x
    by_cases hx : x ∈ C
    · have hx0 : x ≠ 0 := fun h => h0C (h ▸ hx)
      simp [zetaIntegrand, hx0, Set.indicator_of_mem hx, hg]
    · simp [zetaIntegrand, Set.indicator_of_notMem hx]
  have hzeta : zeta T μ.measure (C.indicator (fun _ => (1 : ℂ))) χ s =
      ∫ x in C, g x ∂μ.measure := by
    rw [← integral_indicator hCm, ← hpt]
    rfl
  have hmass : μ.measure C = μ.measure (T.additiveLattice m : Set F.Carrier) := by
    have hCeq : C = (fun z => -(b : F.Carrier) + z) ⁻¹' (T.additiveLattice m : Set F.Carrier) := by
      ext z
      simp only [hCdef, Set.mem_preimage, Set.mem_ofPred_eq, SetLike.mem_coe]
      rw [neg_add_eq_sub]
    rw [hCeq, measure_preimage_add]
  rw [hzeta]
  split_ifs with haj
  · have hc : ∀ x ∈ C, g x = (χ b : ℂ) *
        Complex.exp ((s - 1) * (Real.log (T.normalizedAbs (b : F.Carrier)) : ℂ)) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := exists_principalUnit_of_mem_coset T m b hb hx
      have hwa : w ∈ T.principalUnits a := T.principalUnits_antitone (by omega) hw
      have hχw : χ w = 1 := hχ.1 w ((unitLevel_iff_mem_principalUnits T a w).mpr hwa)
      have habs : T.normalizedAbs ((b : F.Carrier) * w) = T.normalizedAbs (b : F.Carrier) := by
        rw [T.normalizedAbs_mul, normalizedAbs_of_mem_principalUnits T hw, mul_one]
      simp only [hg, characterExtension_unit_mul, characterExtension_unit, hχw, Units.val_one,
        mul_one, habs]
    rw [setIntegral_congr_fun hCm hc, setIntegral_const, measureReal_def, hmass,
      Complex.real_smul]
    ring
  · push Not at haj
    have hlt : (-m - T.ord (b : F.Carrier)).toNat < T.multiplicativeConductor χ := by
      rw [← (conductorAt_iff T χ a).mp hχ]
      omega
    obtain ⟨u, hu, hχu⟩ := T.exists_nontrivial_below_multiplicativeConductor χ _ hlt
    have habsu : T.normalizedAbs (u : F.Carrier) = 1 := normalizedAbs_of_mem_principalUnits T hu
    have hpre : (fun x => (u : F.Carrier) * x) ⁻¹' C = C := by
      ext x
      change (u : F.Carrier) * x - b ∈ T.additiveLattice m ↔ x - b ∈ T.additiveLattice m
      have hub : ((u : F.Carrier) - 1) * b ∈ T.additiveLattice m := by
        rw [T.mem_additiveLattice, map_mul, gauss_valuation_eq_exp_neg_ord T hb0]
        calc T.discreteValuation ((u : F.Carrier) - 1) * WithZero.exp (-T.ord (b : F.Carrier))
            ≤ WithZero.exp (-(((-m - T.ord (b : F.Carrier)).toNat : ℕ) : ℤ)) *
                WithZero.exp (-T.ord (b : F.Carrier)) := mul_le_mul' hu.2 le_rfl
          _ = WithZero.exp m := by
            rw [← WithZero.exp_add, hjn]
            congr 1
            ring
      have hmul : ∀ y : F.Carrier,
          (u : F.Carrier) * y ∈ T.additiveLattice m ↔ y ∈ T.additiveLattice m := by
        intro y
        rw [T.mem_additiveLattice, T.mem_additiveLattice, map_mul, hu.1, one_mul]
      have heq : (u : F.Carrier) * x - b =
          (u : F.Carrier) * (x - b) + ((u : F.Carrier) - 1) * b := by ring
      rw [heq]
      constructor
      · intro h
        have h2 := sub_mem h hub
        rw [add_sub_cancel_right] at h2
        exact (hmul _).mp h2
      · intro h
        exact add_mem ((hmul _).mpr h) hub
    have hrot : ∀ x, g ((u : F.Carrier) * x) = (χ u : ℂ) * g x := by
      intro x
      simp only [hg, characterExtension_unit_mul, T.normalizedAbs_mul, habsu, one_mul]
      ring
    have hI := setIntegral_preimage_mul_unit T μ u C g
    rw [hpre, habsu, inv_one, one_smul] at hI
    simp_rw [hrot] at hI
    rw [integral_const_mul] at hI
    by_contra hne
    apply hχu
    have h1 := (mul_eq_right₀ hne).mp hI
    exact Units.ext (by simpa using h1)

end Langlands.LocalFactor.PadicAbelian
