import Langlands.BaseChange.TwistedCharacter.Basic
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.LinearAlgebra.FiniteRankTensorTrace
import Langlands.HarmonicAnalysis.SchwartzBruhatPiTensor
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Twisted characters of finite external tensor products -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands
open scoped TensorProduct

universe uI uG uV

section Scaling

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Twisted local values do not depend on a positive rescaling of the measure. -/
private theorem hasLocalValue_twisted_of_eq_smul (μ₀ μ : Measure G)
    [IsFiniteMeasureOnCompacts μ₀] [μ₀.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (r : NNReal) (hμ : μ = r • μ₀) (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (A : Module.End ℂ V) {g : G} {c : ℂ}
    (h : HasLocalValue μ₀ (twistedDistribution μ₀ ρ hρ A) g c) :
    HasLocalValue μ (twistedDistribution μ ρ hρ A) g c := by
  obtain ⟨U, hU, hg, hf⟩ := h
  refine ⟨U, hU, hg, fun f hsupp => ?_⟩
  have hact : Hecke.integratedAction μ ρ hρ.1 f =
      (r : ℂ) • Hecke.integratedAction μ₀ ρ hρ.1 f := by
    ext v
    simp only [Hecke.integratedAction_apply, LinearMap.smul_apply]
    rw [hμ]
    simp only [AlgebraicIntegral.integral, Measure.smul_apply, Finset.smul_sum, smul_smul,
      ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.ofReal_mul]
  have hΘ : twistedDistribution μ ρ hρ A f = (r : ℂ) * twistedDistribution μ₀ ρ hρ A f := by
    rw [← smul_eq_mul, ← LinearMap.smul_apply, ← twistedDistribution_smul,
      twistedDistribution_apply, twistedDistribution_apply]
    apply congrArg FiniteRankEnd.trace
    apply Subtype.ext
    change (Hecke.integratedAction μ ρ hρ.1 f).comp A =
      (Hecke.integratedAction μ₀ ρ hρ.1 f).comp ((r : ℂ) • A)
    rw [hact, LinearMap.smul_comp, LinearMap.comp_smul]
  have hint : (∫ y, f y ∂μ) = (r : ℂ) * ∫ y, f y ∂μ₀ := by
    rw [hμ, integral_smul_nnreal_measure]
    rfl
  rw [hΘ, hf f hsupp, hint]
  ring

end Scaling

section External

variable {ι : Type uI} [Fintype ι] [DecidableEq ι]
variable {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)]
variable {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

section IntegratedAction

variable [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

/-- The integrated action of a product test function on a pure tensor is the pure tensor of
the factor integrated actions, for the product of the factor measures. -/
theorem integratedAction_external_tprod (μ : ∀ i, Measure (H i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsSmooth (ρ i))
    (f : ∀ i, SchwartzBruhat (H i)) (v : ∀ i, V i) :
    Hecke.integratedAction (Measure.pi μ) (FiniteTensor.external ρ)
        (FiniteTensor.isSmooth_external ρ hρ) (SchwartzBruhat.piTensor f)
        (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => Hecke.integratedAction (μ i) (ρ i) (hρ i) (f i) (v i)) := by
  classical
  let s (i : ι) := Hecke.actionIntegrand (ρ i) (hρ i) (f i) (v i)
  let t : Finset (∀ i, V i) := Fintype.piFinset fun i => (s i).range
  let S (J : ∀ i, V i) : Set (∀ i, H i) := Set.pi Set.univ fun i => (s i) ⁻¹' {J i}
  rw [Hecke.integratedAction_eq_sum_of_presentation (Measure.pi μ) _ _ _ _ t S
    (fun J => PiTensorProduct.tprod ℂ J)
    (fun J _ => MeasurableSet.univ_pi fun i => (s i).measurableSet_fiber (J i))
    (fun J _ hJ => by
      rw [Measure.pi_pi]
      apply ENNReal.prod_lt_top
      intro i _
      have hJi : J i ≠ 0 := fun h0 => hJ (MultilinearMap.map_coord_zero _ i h0)
      exact (Hecke.actionIntegrand_finMeasSupp (μ i) (ρ i) (hρ i) (f i) (v i)).meas_preimage_singleton_ne_zero
        hJi)
    (fun x => by
      rw [Finset.sum_eq_single (fun i => s i (x i))]
      · have hxS : x ∈ S (fun i => s i (x i)) := Set.mem_univ_pi.mpr fun i => rfl
        rw [Set.indicator_of_mem hxS, SchwartzBruhat.piTensor_apply, FiniteTensor.external_tprod]
        exact (MultilinearMap.map_smul_univ (PiTensorProduct.tprod ℂ) (fun i => f i (x i))
          (fun i => ρ i (x i) (v i))).symm
      · intro J _ hJ
        apply Set.indicator_of_notMem
        intro hx
        apply hJ
        funext i
        exact (Set.mem_singleton_iff.mp (hx i (Set.mem_univ i))).symm
      · intro hnot
        exact absurd (Fintype.mem_piFinset.mpr fun i => (s i).mem_range_self (x i)) hnot)]
  rw [show (fun i => Hecke.integratedAction (μ i) (ρ i) (hρ i) (f i) (v i)) =
      fun i => ∑ w ∈ (s i).range, ((μ i ((s i) ⁻¹' {w})).toReal : ℂ) • w from rfl,
    MultilinearMap.map_sum_finset]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [MultilinearMap.map_smul_univ, Measure.pi_pi, ENNReal.toReal_prod, Complex.ofReal_prod]

variable [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)]

/-- On a product test function, the twisted distribution of the external tensor product
with the tensor endomorphism is the product of the factor twisted distributions. -/
theorem twistedDistribution_external_piTensor (μ : ∀ i, Measure (H i))
    [∀ i, SigmaFinite (μ i)] [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    [∀ i, (μ i).IsMulLeftInvariant]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i)) (f : ∀ i, SchwartzBruhat (H i)) :
    twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
        (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)
        (SchwartzBruhat.piTensor f) =
      ∏ i, twistedDistribution (μ i) (ρ i) (hρ i) (A i) (f i) := by
  rw [twistedDistribution_apply]
  let T : ∀ i, finiteRankEnd (V i) := fun i =>
    ⟨(Character.finiteRankIntegratedAction (μ i) (ρ i) (hρ i) (f i)).val.comp (A i),
      (Character.finiteRankIntegratedAction (μ i) (ρ i) (hρ i) (f i)).property.comp_right (A i)⟩
  have h : (⟨(Character.finiteRankIntegratedAction (Measure.pi μ) (FiniteTensor.external ρ)
      (FiniteTensor.isAdmissible_external ρ hρ) (SchwartzBruhat.piTensor f)).val.comp
        (PiTensorProduct.map A),
      (Character.finiteRankIntegratedAction (Measure.pi μ) (FiniteTensor.external ρ)
      (FiniteTensor.isAdmissible_external ρ hρ) (SchwartzBruhat.piTensor f)).property.comp_right
        (PiTensorProduct.map A)⟩ : finiteRankEnd (⨂[ℂ] i, V i)) =
      FiniteRankEnd.piTensorMap T := by
    apply Subtype.ext
    rw [FiniteRankEnd.piTensorMap_val]
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      Character.finiteRankIntegratedAction_coe, T]
    exact integratedAction_external_tprod μ ρ (fun i => (hρ i).1) f (fun i => A i (v i))
  rw [h, FiniteRankEnd.trace_piTensorMap]
  rfl

end IntegratedAction

variable [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, TotallyDisconnectedSpace (H i)]

/-- Multiplication of test functions by a characteristic function. -/
private def mulTest {X : Type uG} [TopologicalSpace X] (χ : SchwartzBruhat X) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨fun x => f x * χ x, f.locallyConstant.comp₂ χ.locallyConstant (· * ·),
    f.hasCompactSupport.mul_right⟩
  map_add' f f' := by ext x; exact add_mul (f x) (f' x) (χ x)
  map_smul' c f := by ext x; exact mul_assoc c (f x) (χ x)

private theorem mulTest_apply {X : Type uG} [TopologicalSpace X] (χ f : SchwartzBruhat X) (x : X) :
    mulTest χ f x = f x * χ x := rfl

private theorem hasLocalValue_pi [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (μ : ∀ i, Measure (H i)) [∀ i, SigmaFinite (μ i)] [∀ i, (μ i).IsHaarMeasure]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i)) (g : ∀ i, H i) (c : ι → ℂ)
    (h : ∀ i, HasLocalValue (μ i) (twistedDistribution (μ i) (ρ i) (hρ i) (A i)) (g i) (c i)) :
    HasLocalValue (Measure.pi μ) (twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
      (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)) g (∏ i, c i) := by
  classical
  choose U hU hgU hval using h
  have hK : ∀ i, ∃ K : Set (H i), IsCompact K ∧ IsClopen K ∧ g i ∈ K ∧ K ⊆ U i :=
    fun i => exists_isCompact_isClopen_subset (hU i) (hgU i)
  choose K hKc hKo hgK hKU using hK
  let χ : ∀ i, SchwartzBruhat (H i) := fun i => Hecke.TestFunction.characteristic (hKo i) (hKc i)
  let R := mulTest (SchwartzBruhat.piTensor χ)
  let Θ := twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
    (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)
  let I : SchwartzBruhat (∀ i, H i) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ x, φ x ∂(Measure.pi μ)
      map_add' := fun φ ψ => integral_add (φ.integrable _) (ψ.integrable _)
      map_smul' := fun a φ => integral_const_mul a _ }
  refine ⟨Set.pi Set.univ K, isOpen_set_pi Set.finite_univ (fun i _ => (hKo i).isOpen),
    fun i _ => hgK i, fun f hf => ?_⟩
  have hRf : R f = f := by
    ext x
    change f x * ∏ i, χ i (x i) = f x
    by_cases hx : x ∈ Set.pi Set.univ K
    · rw [Finset.prod_eq_one fun i _ => ?_, mul_one]
      change (K i).indicator (fun _ => (1 : ℂ)) (x i) = 1
      exact Set.indicator_of_mem (hx i (Set.mem_univ i)) _
    · have h0 : f x = 0 := Function.notMem_support.mp fun hs => hx (hf hs)
      rw [h0, zero_mul]
  have hker : f ∈ LinearMap.ker (Θ - (∏ i, c i) • I) := by
    rw [← hRf]
    have hmem : f ∈ Submodule.span ℂ (Set.range (SchwartzBruhat.piTensor (X := H))) := by
      rw [SchwartzBruhat.span_piTensor]
      exact Submodule.mem_top
    have hmap : R f ∈ Submodule.span ℂ (R '' Set.range (SchwartzBruhat.piTensor (X := H))) := by
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hmem
    refine (Submodule.span_le.mpr ?_) hmap
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    let k' : ∀ i, SchwartzBruhat (H i) := fun i => mulTest (χ i) (k i)
    have hk : R (SchwartzBruhat.piTensor k) = SchwartzBruhat.piTensor k' := by
      ext x
      change (∏ i, k i (x i)) * ∏ i, χ i (x i) = ∏ i, k i (x i) * χ i (x i)
      rw [Finset.prod_mul_distrib]
    have hsupp : ∀ i, Function.support (k' i) ⊆ U i := by
      intro i x hx
      apply hKU i
      by_contra hxK
      apply hx
      change k i x * (K i).indicator (fun _ => (1 : ℂ)) x = 0
      rw [Set.indicator_of_notMem hxK, mul_zero]
    change Θ (R (SchwartzBruhat.piTensor k)) - (∏ i, c i) * I (R (SchwartzBruhat.piTensor k)) = 0
    rw [hk, sub_eq_zero]
    change twistedDistribution (Measure.pi μ) (FiniteTensor.external ρ)
      (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)
        (SchwartzBruhat.piTensor k') =
      (∏ i, c i) * ∫ x, (∏ i, k' i (x i)) ∂(Measure.pi μ)
    rw [twistedDistribution_external_piTensor μ ρ hρ A k', integral_fintype_prod_eq_prod,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hval i (k' i) (hsupp i)
  have hz := LinearMap.mem_ker.mp hker
  change Θ f - (∏ i, c i) * I f = 0 at hz
  exact sub_eq_zero.mp hz

/-- At a point of the product group, finite external tensor products multiply twisted
character values. -/
theorem hasTwistedCharacterValue_external
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i)) (g : ∀ i, H i) (c : ι → ℂ)
    (h : ∀ i, HasTwistedCharacterValue (ρ i) (hρ i) (A i) (g i) (c i)) :
    HasTwistedCharacterValue (FiniteTensor.external ρ) (FiniteTensor.isAdmissible_external ρ hρ)
      (PiTensorProduct.map A) g (∏ i, c i) := by
  let _ : ∀ i, MeasurableSpace (H i) := fun i => borel (H i)
  have _ : ∀ i, BorelSpace (H i) := fun i => ⟨rfl⟩
  let μ₀ : ∀ i, Measure (H i) := fun i => Measure.haar
  have hloc : ∀ i, HasLocalValue (μ₀ i) (twistedDistribution (μ₀ i) (ρ i) (hρ i) (A i))
      (g i) (c i) := fun i => h i (μ₀ i)
  have hpi := hasLocalValue_pi μ₀ ρ hρ A g c hloc
  have key : ∀ (m' : MeasurableSpace (∀ i, H i)) [BorelSpace (∀ i, H i)]
      (ν : Measure (∀ i, H i)) [ν.IsHaarMeasure],
      HasLocalValue ν (twistedDistribution ν (FiniteTensor.external ρ)
        (FiniteTensor.isAdmissible_external ρ hρ) (PiTensorProduct.map A)) g (∏ i, c i) := by
    intro m' hm' ν hν
    obtain rfl : m' = MeasurableSpace.pi :=
      (@BorelSpace.measurable_eq _ _ m' hm').trans
        (@BorelSpace.measurable_eq _ _ MeasurableSpace.pi Pi.borelSpace).symm
    exact hasLocalValue_twisted_of_eq_smul (Measure.pi μ₀) ν _
      (Measure.isMulLeftInvariant_eq_smul ν (Measure.pi μ₀)) _ _ _ hpi
  let m : MeasurableSpace (∀ i, H i) := borel (∀ i, H i)
  have _ : BorelSpace (∀ i, H i) := ⟨rfl⟩
  intro μ _
  exact key m μ

end External

/-- For finite families of admissible complex representations of second-countable, Hausdorff,
locally compact, totally disconnected groups, factor twisted character values multiply under the
external tensor product and the tensor product of the endomorphisms. -/
def ExternalTensorTwistedCharacterStatement : Prop :=
  ∀ {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {H : ι → Type uG} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, SecondCountableTopology (H i)]
    [∀ i, T2Space (H i)] [∀ i, LocallyCompactSpace (H i)] [∀ i, TotallyDisconnectedSpace (H i)]
    {V : ι → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (H i) (V i)) (hρ : ∀ i, IsAdmissible (ρ i))
    (A : ∀ i, Module.End ℂ (V i)) (g : ∀ i, H i) (c : ι → ℂ),
    (∀ i, HasTwistedCharacterValue (ρ i) (hρ i) (A i) (g i) (c i)) →
    HasTwistedCharacterValue (FiniteTensor.external ρ) (FiniteTensor.isAdmissible_external ρ hρ)
      (PiTensorProduct.map A) g (∏ i, c i)

/-- Proof of `ExternalTensorTwistedCharacterStatement`. -/
theorem externalTensorTwistedCharacterStatement :
    ExternalTensorTwistedCharacterStatement.{uI, uG, uV} := by
  intro ι _ _ H _ _ _ _ _ _ _ V _ _ ρ hρ A g c h
  exact hasTwistedCharacterValue_external ρ hρ A g c h

end Langlands.BaseChange
