import Langlands.Global.RankinSelberg.DualExpansionTorus
import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Langlands.Global.TriangularRationalQuotientCompact

/-! # Normalized periods over `F^ι \ 𝔸^ι` as torus integrals -/

noncomputable section
universe u
open MeasureTheory NumberField Topology Set
open scoped ENNReal Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.Automorphic.CuspidalWhittaker

variable (F : Type u) [Field F] [NumberField F] (ι : Type) [Fintype ι]

/-- The adelic vector group `𝔸^ι`, written multiplicatively. -/
abbrev ColGroup := Multiplicative (ι → Adeles F)

instance colGroupMeasurableSpace : MeasurableSpace (ColGroup F ι) := borel _

instance colGroupBorelSpace : BorelSpace (ColGroup F ι) := ⟨rfl⟩

instance colGroupSecondCountable : SecondCountableTopology (ColGroup F ι) := by
  have := adeles_secondCountableTopology F
  exact (inferInstance : SecondCountableTopology (ι → Adeles F))

instance colGroupLocallyCompact : LocallyCompactSpace (ColGroup F ι) := by
  have := adeles_locallyCompactSpace F
  exact (inferInstance : LocallyCompactSpace (ι → Adeles F))

/-- The rational lattice `F^ι` in `𝔸^ι`. -/
def ratLattice : Subgroup (ColGroup F ι) where
  carrier := {x | ∃ k : ι → F, Multiplicative.toAdd x = ratVec k}
  one_mem' := ⟨0, by rw [ratVec_zero]; rfl⟩
  mul_mem' := by
    rintro x y ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by rw [toAdd_mul, hk, hl, ratVec_add]⟩
  inv_mem' := by
    rintro x ⟨k, hk⟩
    exact ⟨-k, by rw [toAdd_inv, hk, ratVec_neg]⟩

omit [Fintype ι] in
theorem mem_ratLattice_iff (x : ColGroup F ι) :
    x ∈ ratLattice F ι ↔ ∃ k : ι → F, Multiplicative.toAdd x = ratVec k := Iff.rfl

theorem isDiscrete_ratLattice : IsDiscrete (ratLattice F ι : Set (ColGroup F ι)) := by
  rw [isDiscrete_iff_discreteTopology]
  change DiscreteTopology (ratLattice F ι)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let U : Set (ColGroup F ι) :=
    {x | ∀ i, Multiplicative.toAdd x i ∈ principalAdelesIsolatingSet F}
  have hU : IsOpen U := by
    have : U = Multiplicative.toAdd ⁻¹' Set.pi univ fun _ => principalAdelesIsolatingSet F := by
      ext x; simp [U]
    rw [this]
    exact (isOpen_set_pi finite_univ fun i _ => isOpen_principalAdelesIsolatingSet F).preimage
      continuous_id
  refine ⟨U, hU, ?_⟩
  ext ⟨x, k, hk⟩
  simp only [mem_preimage, mem_singleton_iff, U]
  constructor
  · intro hx
    apply Subtype.ext
    change x = 1
    have hk0 : ∀ i, algebraMap F (Adeles F) (k i) = 0 := by
      intro i
      have h1 := hx i
      rw [hk, ratVec_apply] at h1
      have h2 : algebraMap F (Adeles F) (k i) ∈ principalAdelesIsolatingSet F ∩
          (principalAdeles F : Set (Adeles F)) := ⟨h1, ⟨k i, rfl⟩⟩
      rw [principalAdelesIsolatingSet_inter_principalAdeles] at h2
      exact Set.mem_singleton_iff.mp h2
    have : Multiplicative.toAdd x = 0 := by
      rw [hk]; funext i; rw [ratVec_apply, hk0 i]; rfl
    exact this
  · intro hx i
    have : x = 1 := congrArg Subtype.val hx
    subst this
    exact zero_mem_principalAdelesIsolatingSet F

omit [Fintype ι] in
theorem exists_isCompact_ratLattice_mul_mem :
    ∃ B : Set (ColGroup F ι), IsCompact B ∧ ∀ g, ∃ p ∈ ratLattice F ι, p * g ∈ B := by
  obtain ⟨D, hDc, hD⟩ := AdelicGroupPoints.exists_isCompact_algebraMap_add_mem F
  refine ⟨Multiplicative.toAdd ⁻¹' Set.pi univ fun _ => D, ?_, fun g => ?_⟩
  · exact isCompact_univ_pi fun _ => hDc
  · choose f hf using fun i => hD (Multiplicative.toAdd g i)
    refine ⟨Multiplicative.ofAdd (ratVec f), ⟨f, rfl⟩, fun i _ => ?_⟩
    simpa [ratVec] using hf i

instance compactSpace_ratLattice_quotient [CompactSpace (AdeleQuotient F)] :
    CompactSpace (LeftCosetSpace (ratLattice F ι)) := by
  obtain ⟨B, hB, hcov⟩ := exists_isCompact_ratLattice_mul_mem F ι
  refine ⟨?_⟩
  have himg : LeftCosetSpace.mk (ratLattice F ι) '' B = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨g, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    obtain ⟨p, hp, hpg⟩ := hcov g
    exact ⟨p * g, hpg, LeftCosetSpace.mk_subgroup_mul _ ⟨p, hp⟩ g⟩
  rw [← himg]
  exact hB.image (LeftCosetSpace.continuous_mk _)

section Period

variable [CompactSpace (AdeleQuotient F)]

omit [CompactSpace (AdeleQuotient F)] in
theorem isFiniteMeasure_haarQuotientMeasure_ratLattice :
    IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure (ratLattice F ι)
      (isDiscrete_ratLattice F ι)) := by
  obtain ⟨B, hB, hcov⟩ := exists_isCompact_ratLattice_mul_mem F ι
  exact LeftCosetSpace.isFiniteMeasure_haarQuotientMeasure_of_isCompact _ _ hB hcov

/-- The reduction map `𝔸^ι → (𝔸/F)^ι`. -/
def colReduce (x : ColGroup F ι) : ι → AdeleQuotient F := torusMk (Multiplicative.toAdd x)

omit [Fintype ι] [CompactSpace (AdeleQuotient F)] in
theorem continuous_colReduce : Continuous (colReduce F ι) :=
  continuous_torusMk.comp continuous_toAdd

omit [Fintype ι] [CompactSpace (AdeleQuotient F)] in
theorem colReduce_mul (a x : ColGroup F ι) :
    colReduce F ι (a * x) = colReduce F ι a + colReduce F ι x := by
  simp only [colReduce, toAdd_mul, torusMk_add]

omit [Fintype ι] [CompactSpace (AdeleQuotient F)] in
theorem colReduce_of_mem (p : ColGroup F ι) (hp : p ∈ ratLattice F ι) (x : ColGroup F ι) :
    colReduce F ι (p * x) = colReduce F ι x := by
  obtain ⟨k, hk⟩ := hp
  rw [colReduce_mul]
  have : colReduce F ι p = 0 := by
    simp only [colReduce, hk, torusMk_ratVec]
  rw [this, zero_add]

/-- The pushforward of Haar measure restricted to a fundamental domain is the corresponding
multiple of the Haar probability measure of the torus. -/
theorem map_colReduce_restrict :
    Measure.map (colReduce F ι) ((Measure.haar : Measure (ColGroup F ι)).restrict
        (LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι))) =
      (Measure.haar : Measure (ColGroup F ι))
          (LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι)) •
        torusHaar F ι := by
  set μ := (Measure.haar : Measure (ColGroup F ι))
  set E := LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι)
  have := isFiniteMeasure_haarQuotientMeasure_ratLattice F ι
  have hEtop : μ E ≠ ⊤ :=
    LeftCosetSpace.haar_fundamentalDomain_ne_top _ (isDiscrete_ratLattice F ι)
  have hπm : Measurable (colReduce F ι) := (continuous_colReduce F ι).measurable
  have hE : IsFundamentalDomain (ratLattice F ι) E μ :=
    LeftCosetSpace.isFundamentalDomain _ (isDiscrete_ratLattice F ι) μ
  set ν := Measure.map (colReduce F ι) (μ.restrict E) with hν
  have : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hEtop.lt_top⟩
  have hfin : IsFiniteMeasure ν := Measure.isFiniteMeasure_map _ _
  have hinv : ν.IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    obtain ⟨a, rfl⟩ := torusMk_surjective (K := F) (ι := ι) t
    set c : ColGroup F ι := Multiplicative.ofAdd a
    have hcomp : (fun s => torusMk a + s) ∘ colReduce F ι = colReduce F ι ∘ (c * ·) := by
      funext x
      simp only [Function.comp, colReduce_mul]
      rfl
    rw [hν, Measure.map_map (measurable_const_add _) hπm, hcomp,
      ← Measure.map_map hπm (measurable_const_mul c)]
    have hshift : Measure.map (c * ·) (μ.restrict E) = μ.restrict ((c⁻¹ * ·) ⁻¹' E) := by
      have hs : MeasurableSet ((c⁻¹ * ·) ⁻¹' E) :=
        (measurable_const_mul _) (LeftCosetSpace.measurableSet_fundamentalDomain _ _)
      have h := Measure.restrict_map (μ := μ) (measurable_const_mul c) hs
      rw [map_mul_left_eq_self] at h
      rw [h]
      congr 2
      ext x
      simp
    rw [hshift]
    have hE' : IsFundamentalDomain (ratLattice F ι) ((c⁻¹ * ·) ⁻¹' E) μ :=
      hE.preimage_of_equiv (quasiMeasurePreserving_mul_left μ c⁻¹) Function.bijective_id
        (fun p x => by simp [Subgroup.smul_def, mul_left_comm])
    ext S hS
    rw [Measure.map_apply hπm hS, Measure.map_apply hπm hS, Measure.restrict_apply (hπm hS),
      Measure.restrict_apply (hπm hS)]
    have := LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_ratLattice F ι)
    refine hE'.measure_set_eq hE (hπm hS) fun p => ?_
    ext x
    simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul]
    rw [colReduce_of_mem F ι _ p.property]
  have hcpt : IsFiniteMeasureOnCompacts ν := inferInstance
  have heq := MeasureTheory.Measure.isAddLeftInvariant_eq_smul ν (torusHaar F ι)
  have hνuniv : ν univ = μ E := by
    rw [hν, Measure.map_apply hπm MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  set c := ν.addHaarScalarFactor (torusHaar F ι) with hcdef
  have hc : ((c : NNReal) : ℝ≥0∞) = μ E := by
    have h := congrArg (fun ρ : Measure (ι → AdeleQuotient F) => ρ univ) heq
    simp only [Measure.smul_apply, measure_univ] at h
    rw [← hνuniv, h]
    simp
  calc ν = c • torusHaar F ι := heq
    _ = μ E • torusHaar F ι := by
      ext s hs
      simp only [Measure.smul_apply, ← hc]
      rfl

/-- The normalized period over `F^ι \ 𝔸^ι` of a continuous periodic function is its torus
integral. -/
theorem normalizedPeriod_ratLattice (f : ColGroup F ι → ℂ) (hf : Continuous f)
    (hfΓ : ∀ p ∈ ratLattice F ι, ∀ x, f (p * x) = f x) :
    ((Measure.haar : Measure (ColGroup F ι))
        (LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι))).toReal⁻¹ •
      ∫ x in LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι), f x
        ∂Measure.haar = torusIntegral ι (fun y => f (Multiplicative.ofAdd y)) := by
  set μ := (Measure.haar : Measure (ColGroup F ι))
  set E := LeftCosetSpace.fundamentalDomain (ratLattice F ι) (isDiscrete_ratLattice F ι)
  have := isFiniteMeasure_haarQuotientMeasure_ratLattice F ι
  have hEtop : μ E ≠ ⊤ :=
    LeftCosetSpace.haar_fundamentalDomain_ne_top _ (isDiscrete_ratLattice F ι)
  have hE0 : μ E ≠ 0 :=
    LeftCosetSpace.haar_fundamentalDomain_ne_zero _ (isDiscrete_ratLattice F ι)
  have hper : IsPeriodic (fun y : ι → Adeles F => f (Multiplicative.ofAdd y)) := by
    intro y k
    show f (Multiplicative.ofAdd (y + ratVec k)) = f (Multiplicative.ofAdd y)
    have := hfΓ (Multiplicative.ofAdd (ratVec k)) ⟨k, rfl⟩ (Multiplicative.ofAdd y)
    rw [← this]
    congr 1
    change Multiplicative.ofAdd (y + ratVec k) = Multiplicative.ofAdd (ratVec k + y)
    rw [add_comm]
  have hc : Continuous (fun y : ι → Adeles F => f (Multiplicative.ofAdd y)) :=
    hf.comp continuous_ofAdd
  set g : (ι → AdeleQuotient F) → ℂ := fun t => f (Multiplicative.ofAdd (torusLift t))
  have hg : Continuous g := hper.continuous_lift hc
  have hfg : ∀ x, f x = g (colReduce F ι x) := by
    intro x
    exact (hper.lift_mk (Multiplicative.toAdd x)).symm
  have hπm : Measurable (colReduce F ι) := (continuous_colReduce F ι).measurable
  have h1 : ∫ x in E, f x ∂μ = ∫ t, g t ∂(Measure.map (colReduce F ι) (μ.restrict E)) := by
    rw [integral_map hπm.aemeasurable hg.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ hfg)
  rw [h1, map_colReduce_restrict, integral_smul_measure, smul_smul, inv_mul_cancel₀
    (ENNReal.toReal_ne_zero.mpr ⟨hE0, hEtop⟩), one_smul]
  rfl

end Period

end Langlands.Global.RankinSelbergGlobal.Unfolding
