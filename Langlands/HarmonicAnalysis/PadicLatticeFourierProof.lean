import Langlands.HarmonicAnalysis.PadicLatticeFourierStatement
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Plus-sign Fourier integrals of p-adic lattice cosets

A coset of a compact open additive subgroup has a convergent plus-sign Fourier
integrand. Translation invariance moves the coset to the subgroup, and
orthogonality on the subgroup leaves its mass or zero. For the valuation lattice
`π^(-m) O` the annihilator is `π^(-(n-m)) O`, by the conductor API.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

section CompactOpenCoset

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

omit [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F] in
/-- The Fourier integrand of a coset indicator is the character restricted to the coset. -/
private theorem coset_integrand_eq (ψ : UnitaryAdditiveCharacter F) (L : AddSubgroup F)
    (a y : F) :
    (fun x => ψ.complex (x * y) * {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) x) =
      {x | x - a ∈ L}.indicator (fun x => ψ.complex (x * y)) := by
  funext x
  by_cases hx : x ∈ {x | x - a ∈ L}
  · simp only [Set.indicator_of_mem hx, mul_one]
  · simp only [Set.indicator_of_notMem hx, mul_zero]

/-- The plus-sign Fourier integrand of the indicator of a coset of a compact
open subgroup is integrable for every Haar measure. -/
theorem coset_fourierIntegrand_integrable (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (L : AddSubgroup F) (hLc : IsCompact (L : Set F))
    (hLo : IsOpen (L : Set F)) (a y : F) :
    Integrable
      (fun x => ψ.complex (x * y) * {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) x)
      μ.measure := by
  have hCo : IsOpen {x : F | x - a ∈ L} :=
    hLo.preimage (continuous_id.sub continuous_const)
  have hCc : IsCompact {x : F | x - a ∈ L} := by
    have hC : {x : F | x - a ∈ L} = (fun t => t + a) '' (L : Set F) := by
      ext x
      constructor
      · intro hx
        exact ⟨x - a, hx, sub_add_cancel x a⟩
      · rintro ⟨t, ht, rfl⟩
        simpa only [Set.mem_ofPred_eq, add_sub_cancel_right, SetLike.mem_coe] using ht
    rw [hC]
    exact hLc.image (continuous_id.add continuous_const)
  rw [coset_integrand_eq]
  apply (integrable_indicator_iff hCo.measurableSet).mpr
  exact (ψ.continuous_complex.comp (continuous_id.mul continuous_const)).continuousOn
    |>.integrableOn_compact' hCc hCo.measurableSet

/-- Translating the coset `a + L` to `L` extracts the plus-sign phase `ψ(a*y)`. -/
theorem coset_fourierIntegral_eq (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (L : AddSubgroup F) (a y : F) :
    fourierIntegral ψ μ ({x | x - a ∈ L}.indicator (fun _ => (1 : ℂ))) y =
      ψ.complex (a * y) *
        ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure := by
  unfold fourierIntegral
  calc
    ∫ x, ψ.complex (x * y) * {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) x ∂μ.measure =
        ∫ t, ψ.complex ((a + t) * y) *
          {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) (a + t) ∂μ.measure :=
      (integral_add_left_eq_self
        (fun x => ψ.complex (x * y) * {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) x)
        a).symm
    _ = ∫ t, ψ.complex (a * y) *
          (ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t) ∂μ.measure := by
      apply integral_congr_ae
      refine ae_of_all _ fun t => ?_
      have hmem : (a + t ∈ {x | x - a ∈ L}) ↔ t ∈ (L : Set F) := by
        simp only [Set.mem_ofPred_eq, add_sub_cancel_left, SetLike.mem_coe]
      change ψ.complex ((a + t) * y) *
          {x | x - a ∈ L}.indicator (fun _ => (1 : ℂ)) (a + t) =
        ψ.complex (a * y) * (ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t)
      rw [add_mul, ψ.complex.map_add_eq_mul, mul_assoc]
      by_cases ht : t ∈ (L : Set F)
      · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem (fun h => ht (hmem.mp h)), Set.indicator_of_notMem ht]
    _ = ψ.complex (a * y) *
          ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure :=
      integral_const_mul _ _

omit [IsTopologicalRing F] in
/-- If `t ↦ ψ(t*y)` is trivial on the open subgroup `L`, the character
integral over `L` is the mass of `L`. -/
theorem subgroup_character_integral_of_trivial (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (L : AddSubgroup F) (hLo : IsOpen (L : Set F)) (y : F)
    (h : ∀ t ∈ L, ψ (t * y) = 1) :
    ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure =
      ((μ.measure (L : Set F)).toReal : ℂ) := by
  calc
    ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure =
        ∫ t, (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure := by
      apply integral_congr_ae
      refine ae_of_all _ fun t => ?_
      by_cases ht : t ∈ (L : Set F)
      · simp only [Set.indicator_of_mem ht, UnitaryAdditiveCharacter.complex_apply,
          h t ht, Circle.coe_one, mul_one]
      · simp only [Set.indicator_of_notMem ht, mul_zero]
    _ = ((μ.measure (L : Set F)).toReal : ℂ) := by
      rw [integral_indicator_const _ hLo.measurableSet, measureReal_def,
        Complex.real_smul, mul_one]

/-- Orthogonality on a subgroup: if `ψ(t₀*y) ≠ 1` for some `t₀ ∈ L`, then the
character integral over `L` vanishes, by translation invariance under `t₀`. -/
theorem subgroup_character_integral_of_nontrivial (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (L : AddSubgroup F) (y t₀ : F) (ht₀ : t₀ ∈ L)
    (hne : ψ (t₀ * y) ≠ 1) :
    ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure = 0 := by
  set I := ∫ t, ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t ∂μ.measure
  have he : ψ.complex (t₀ * y) * I = I := by
    calc
      ψ.complex (t₀ * y) * I =
          ∫ t, ψ.complex (t₀ * y) *
            (ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t) ∂μ.measure :=
        (integral_const_mul _ _).symm
      _ = ∫ t, ψ.complex ((t₀ + t) * y) *
            (L : Set F).indicator (fun _ => (1 : ℂ)) (t₀ + t) ∂μ.measure := by
        apply integral_congr_ae
        refine ae_of_all _ fun t => ?_
        have hmem : t₀ + t ∈ (L : Set F) ↔ t ∈ (L : Set F) :=
          L.add_mem_cancel_left ht₀
        change ψ.complex (t₀ * y) *
            (ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t) =
          ψ.complex ((t₀ + t) * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) (t₀ + t)
        rw [add_mul, ψ.complex.map_add_eq_mul, mul_assoc]
        by_cases ht : t ∈ (L : Set F)
        · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem (fun h => ht (hmem.mp h)),
            Set.indicator_of_notMem ht]
      _ = I :=
        integral_add_left_eq_self
          (fun t => ψ.complex (t * y) * (L : Set F).indicator (fun _ => (1 : ℂ)) t) t₀
  by_contra hIz
  apply hne
  apply Circle.coe_eq_one.mp
  simpa only [UnitaryAdditiveCharacter.complex_apply] using (mul_eq_right₀ hIz).mp he

end CompactOpenCoset

end Langlands.HarmonicAnalysis

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology

/-- The `ψ`-annihilator of `π^(-m) O` is `π^(-(n(ψ)-m)) O`. -/
theorem forall_mul_eq_one_iff_mem_additiveLattice (ψ : AdditiveCharacter) (m : ℤ)
    (y : F.Carrier) :
    (∀ t ∈ T.additiveLattice m, ψ (t * y) = 1) ↔
      y ∈ T.additiveLattice (T.additiveConductor ψ - m) := by
  constructor
  · intro h
    apply T.mem_additiveLattice_of_forall_mul_eq_one ψ m y
    intro x hx
    rw [mul_comm]
    exact h x hx
  · intro hy t ht
    apply (T.additiveConductor_spec ψ).1
    rw [mem_additiveLattice, map_mul]
    calc
      T.discreteValuation t * T.discreteValuation y ≤
          WithZero.exp m * WithZero.exp (T.additiveConductor ψ - m) :=
        mul_le_mul' ht hy
      _ = WithZero.exp (T.additiveConductor ψ) := by
        rw [← WithZero.exp_add, add_sub_cancel]

end Langlands.PadicField.TopologicalData

namespace Langlands.HarmonicAnalysis

universe u

/-- The published lattice-coset Fourier proposition, for every supplied topology. -/
theorem padicLatticeFourier {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicLatticeFourierStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  intro ψ μ m a y C indicatorC
  refine ⟨coset_fourierIntegrand_integrable ψ μ (T.additiveLattice m)
    (T.isCompact_additiveLattice m) (T.isOpen_additiveLattice m) a y, ?_⟩
  rw [coset_fourierIntegral_eq]
  by_cases hy : y ∈ T.additiveLattice (T.additiveConductor ψ - m)
  · rw [subgroup_character_integral_of_trivial ψ μ (T.additiveLattice m)
      (T.isOpen_additiveLattice m) y
      ((T.forall_mul_eq_one_iff_mem_additiveLattice ψ m y).mpr hy),
      Set.indicator_of_mem (SetLike.mem_coe.mpr hy), mul_one, mul_comm]
  · have hnt : ¬ ∀ t ∈ T.additiveLattice m, ψ (t * y) = 1 :=
      fun h => hy ((T.forall_mul_eq_one_iff_mem_additiveLattice ψ m y).mp h)
    push Not at hnt
    obtain ⟨t₀, ht₀, hne⟩ := hnt
    rw [subgroup_character_integral_of_nontrivial ψ μ (T.additiveLattice m) y t₀ ht₀ hne,
      Set.indicator_of_notMem (fun h => hy (SetLike.mem_coe.mp h)), mul_zero, mul_zero]

end Langlands.HarmonicAnalysis
