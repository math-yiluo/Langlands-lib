import Langlands.Global.LeftCosetSemidirectFiniteVolume
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Period reduction for split lattices in semidirect products -/

noncomputable section

universe u v w z

open MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace.Semidirect

variable {N : Type u} {M : Type v} {H : Type w}
  [Group N] [Group M] [Group H]
  (i : N →* H) (j : M →* H) (p : H →* M)
  (hpj : ∀ m, p (j m) = m)
  (hker : ∀ h, p h = 1 → ∃ n, i n = h)
  (hpi : ∀ n, p (i n) = 1)
  [TopologicalSpace N] [TopologicalSpace M] [TopologicalSpace H]
  [IsTopologicalGroup N] [IsTopologicalGroup M] [IsTopologicalGroup H]
  [SecondCountableTopology N] [SecondCountableTopology M] [SecondCountableTopology H]
  [LocallyCompactSpace N] [LocallyCompactSpace M] [LocallyCompactSpace H]
  [MeasurableSpace N] [MeasurableSpace M] [MeasurableSpace H]
  [BorelSpace N] [BorelSpace M] [BorelSpace H]
  (hi : IsEmbedding i) (hj : Continuous j) (hp : Continuous p)
  (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
  (ΓM : Subgroup M) (hΓM : IsDiscrete (ΓM : Set M))
  (hjΓ : ∀ m ∈ ΓM, j m ∈ Γ) (hpΓ : ∀ h ∈ Γ, p h ∈ ΓM)

/-- The product of the chosen normal and complement lattice transversals in `H`. -/
def productFundamentalDomain
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N)) : Set H :=
  prodHomeomorph i j p hpj hker hpi hi hj hp ''
    (fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM)

omit [SecondCountableTopology H] [LocallyCompactSpace N] [LocallyCompactSpace M]
  [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] in
include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- Product transversals give a genuine transversal for a split lattice. -/
theorem productFundamentalDomain_unique
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N)) (h : H) :
    ∃! γ : Γ, (γ : H) * h ∈
      prodHomeomorph i j p hpj hker hpi hi hj hp ''
        (fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM) := by
  classical
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  obtain ⟨⟨n, m⟩, rfl⟩ := Φ.surjective h
  obtain ⟨γM, hγM, hγMu⟩ := fundamentalDomain_unique ΓM hΓM m
  obtain ⟨γN, hγN, hγNu⟩ := fundamentalDomain_unique (Γ.comap i) hΓN
    (conj i j p hpj hker hpi hi hj γM n)
  let γ : Γ := ⟨i γN * j γM, Γ.mul_mem γN.property (hjΓ γM γM.property)⟩
  have hγ : (γ : H) * Φ (n, m) =
      Φ (γN * conj i j p hpj hker hpi hi hj γM n, γM * m) :=
    i_mul_j_mul_i_mul_j i j p hpj hker hpi hi hj n γN m γM
  refine ⟨γ, ⟨_, ⟨hγN, hγM⟩, hγ.symm⟩, ?_⟩
  intro δ hδ
  obtain ⟨⟨n', m'⟩, ⟨hn', hm'⟩, hδ⟩ := hδ
  have hm'eq : m' = p δ * m := by
    have heq := congrArg p hδ
    simpa only [Φ, prodHomeomorph_apply, map_mul, hpi, hpj, one_mul] using heq
  have hpδeq : (⟨p δ, hpΓ δ δ.property⟩ : ΓM) = γM := by
    apply hγMu
    simpa only [Subtype.coe_mk, ← hm'eq] using hm'
  have hpδ : p δ = γM := congrArg Subtype.val hpδeq
  let δN : Γ.comap i := ⟨normalPart i j p hpj hker δ, by
    change i (normalPart i j p hpj hker δ) ∈ Γ
    rw [i_normalPart, hpδ]
    exact Γ.mul_mem δ.property (Γ.inv_mem (hjΓ γM γM.property))⟩
  have hδrep : (δ : H) = i δN * j γM := by
    simpa only [δN, Subtype.coe_mk, hpδ] using
      (i_normalPart_mul_j_p i j p hpj hker (δ : H)).symm
  have hn'eq : n' = δN * conj i j p hpj hker hpi hi hj γM n := by
    have heq : Φ (n', m') =
        Φ (δN * conj i j p hpj hker hpi hi hj γM n, γM * m) := by
      rw [hδ, hδrep]
      exact i_mul_j_mul_i_mul_j i j p hpj hker hpi hi hj n δN m γM
    exact congrArg Prod.fst (Φ.injective heq)
  have hδN : δN = γN := hγNu δN (by simpa only [← hn'eq] using hn')
  apply Subtype.ext
  rw [hδrep, hδN]

omit [SecondCountableTopology H] [LocallyCompactSpace N] [LocallyCompactSpace M] in
include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- The product transversal is a measurable fundamental domain for the full lattice. -/
theorem isFundamentalDomain_product
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N)) :
    IsFundamentalDomain Γ
      (prodHomeomorph i j p hpj hker hpi hi hj hp ''
        (fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM))
      (Measure.haar : Measure H) := by
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  have hS : MeasurableSet (Φ ''
      (fundamentalDomain (Γ.comap i) hΓN ×ˢ fundamentalDomain ΓM hΓM)) := by
    rw [Φ.image_eq_preimage_symm]
    exact Φ.symm.continuous.measurable
      ((measurableSet_fundamentalDomain (Γ.comap i) hΓN).prod
        (measurableSet_fundamentalDomain ΓM hΓM))
  exact IsFundamentalDomain.mk' hS.nullMeasurableSet
    (productFundamentalDomain_unique i j p hpj hker hpi hi hj hp Γ ΓM hΓM hjΓ hpΓ hΓN)

omit [SecondCountableTopology H] [LocallyCompactSpace H]
  [MeasurableSpace H] [BorelSpace H] in
include hpj hker hpi hi hj hjΓ in
/-- Finite covolumes force every complement conjugation to preserve normal Haar measure. -/
theorem mulEquivHaarChar_conj_eq_one_of_finiteCovolume
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N))
    [IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN)]
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)] (m : M) :
    mulEquivHaarChar (conj i j p hpj hker hpi hi hj m) = 1 := by
  refine eq_one_of_measurable_of_isFiniteMeasure ΓM hΓM _
    (measurable_mulEquivHaarChar_conj hpj hker hpi hi hj)
    (mulEquivHaarChar_conj_mul hpj hker hpi hi hj)
    (fun m => (mulEquivHaarChar_pos _).ne') ?_ m
  intro γ hγ
  refine mulEquivHaarChar_eq_one_of_forall_mem_iff (Γ.comap i) hΓN _ fun n => ?_
  simp only [Subgroup.mem_comap, i_conj]
  constructor
  · intro hn
    have hn' := Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (hjΓ γ hγ)) hn) (hjΓ γ hγ)
    have heq : (j γ)⁻¹ * (j γ * i n * (j γ)⁻¹) * j γ = i n := by group
    rwa [heq] at hn'
  · intro hn
    exact Γ.mul_mem (Γ.mul_mem (hjΓ γ hγ) hn) (Γ.inv_mem (hjΓ γ hγ))

include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- Vanishing normal periods imply vanishing total period, for bounded continuous
lattice-invariant functions and finite normal and complement covolumes. -/
theorem integral_fundamentalDomain_eq_zero_of_bounded
    (hΓN : IsDiscrete ((Γ.comap i : Subgroup N) : Set N))
    [IsFiniteMeasure (haarQuotientMeasure (Γ.comap i) hΓN)]
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h)
    (hbound : ∃ C : ℝ, ∀ h, ‖φ h‖ ≤ C)
    (hN : ∀ m : M, ∫ n in fundamentalDomain (Γ.comap i) hΓN,
      φ (i n * j m) ∂Measure.haar = 0) :
    ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar = 0 := by
  classical
  let Φ := prodHomeomorph i j p hpj hker hpi hi hj hp
  let EN := fundamentalDomain (Γ.comap i) hΓN
  let EM := fundamentalDomain ΓM hΓM
  let ν := (Measure.haar : Measure N).prod (Measure.haar : Measure M)
  obtain ⟨c, hc⟩ := exists_haar_eq_smul_map_prod hpj hker hpi hi hj hp
    (mulEquivHaarChar_conj_eq_one_of_finiteCovolume
      i j p hpj hker hpi hi hj Γ ΓM hΓM hjΓ hΓN)
  have hEN : (Measure.haar : Measure N) EN < ∞ :=
    (haar_fundamentalDomain_ne_top (Γ.comap i) hΓN).lt_top
  have hEM : (Measure.haar : Measure M) EM < ∞ :=
    (haar_fundamentalDomain_ne_top ΓM hΓM).lt_top
  have : IsFiniteMeasure ((Measure.haar : Measure N).restrict EN) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hEN⟩
  have : IsFiniteMeasure ((Measure.haar : Measure M).restrict EM) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hEM⟩
  have hI : IntegrableOn (fun x : N × M => φ (Φ x)) (EN ×ˢ EM) ν := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    obtain ⟨C, hC⟩ := hbound
    exact ⟨(hφ.comp Φ.continuous).stronglyMeasurable.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (ae_of_all _ fun x => hC (Φ x))⟩
  have hdomain := isFundamentalDomain_product
    i j p hpj hker hpi hi hj hp Γ ΓM hΓM hjΓ hpΓ hΓN
  have : Countable Γ := countable_of_isDiscrete Γ hΓ
  rw [(isFundamentalDomain Γ hΓ Measure.haar).setIntegral_eq hdomain
    (fun γ h => hφΓ γ γ.property h)]
  rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure]
  change c • (∫ h in Φ '' (EN ×ˢ EM), φ h ∂ν.map Φ) = 0
  rw [Φ.isClosedEmbedding.setIntegral_map, Φ.preimage_image]
  have hFubini :
      ∫ x in EN ×ˢ EM, φ (Φ x) ∂ν =
        ∫ m in EM, ∫ n in EN, φ (i n * j m) ∂Measure.haar ∂Measure.haar := by
    rw [← Measure.prod_restrict]
    rw [IntegrableOn, ← Measure.prod_restrict] at hI
    exact integral_prod_symm _ hI
  rw [hFubini]
  simp only [EN, hN, integral_zero, smul_zero]

include hpj hker hpi hi hj hp hjΓ hpΓ in
/-- On a compact full quotient the boundedness needed for period reduction is automatic.
The normal lattice is supplied separately for use with concrete rational subgroups. -/
theorem integral_fundamentalDomain_eq_zero
    (ΓN : Subgroup N) (hΓN : IsDiscrete (ΓN : Set N))
    (hiΓ : ∀ n, i n ∈ Γ ↔ n ∈ ΓN)
    [IsFiniteMeasure (haarQuotientMeasure ΓN hΓN)]
    [IsFiniteMeasure (haarQuotientMeasure ΓM hΓM)]
    [CompactSpace (Langlands.Global.LeftCosetSpace Γ)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h)
    (hN : ∀ m : M, ∫ n in fundamentalDomain ΓN hΓN,
      φ (i n * j m) ∂Measure.haar = 0) :
    ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar = 0 := by
  have heq : Γ.comap i = ΓN := Subgroup.ext hiΓ
  subst ΓN
  let f := lift Γ φ (fun γ h => hφΓ γ γ.property h)
  have hf : Continuous f := continuous_lift Γ _ _ hφ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact integral_fundamentalDomain_eq_zero_of_bounded
    i j p hpj hker hpi hi hj hp Γ hΓ ΓM hΓM hjΓ hpΓ hΓN φ hφ hφΓ
    ⟨C, fun h => hC (mk Γ h) (mem_univ _)⟩ hN

include hpj hker hpi hi hj hp hΓM hjΓ hpΓ in
/-- Compact quotients supply both finite covolumes and convergence of the iterated period. -/
theorem integral_fundamentalDomain_eq_zero_of_compact
    (ΓN : Subgroup N) (hΓN : IsDiscrete (ΓN : Set N))
    (hiΓ : ∀ n, i n ∈ Γ ↔ n ∈ ΓN)
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓN)]
    [CompactSpace (Langlands.Global.LeftCosetSpace ΓM)]
    [CompactSpace (Langlands.Global.LeftCosetSpace Γ)]
    (φ : H → ℂ) (hφ : Continuous φ)
    (hφΓ : ∀ γ ∈ Γ, ∀ h, φ (γ * h) = φ h)
    (hN : ∀ m : M, ∫ n in fundamentalDomain ΓN hΓN,
      φ (i n * j m) ∂Measure.haar = 0) :
    ∫ h in fundamentalDomain Γ hΓ, φ h ∂Measure.haar = 0 := by
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓN hΓN
  have := isLocallyFiniteMeasure_haarQuotientMeasure ΓM hΓM
  exact integral_fundamentalDomain_eq_zero
    i j p hpj hker hpi hi hj hp Γ hΓ ΓM hΓM hjΓ hpΓ ΓN hΓN hiΓ φ hφ hφΓ hN

end Langlands.Global.LeftCosetSpace.Semidirect
