import Langlands.Global.LeftCosetHaarMeasure
import Langlands.Analysis.Local.InvolutiveHaarCharacter
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

/-! # Automorphisms of discrete left quotients and their quotient measures

An automorphism `α` of a group `H` carrying a subgroup `Γ` onto itself induces a bijection of
`Γ \ H`. It carries the quotient measure of `ν` restricted to `s` to the quotient measure of
`α_* ν` restricted to `α (s)`. When `Γ` is discrete and `α_* ν = c ν`, the induced map scales
the fundamental-domain quotient measure by `c`; consequently it preserves the quotient measure
normalized by its total mass, whatever the value of `c`. For the actual Haar measure the factor
is the inverse of Mathlib's `mulEquivHaarChar`, which equals `1` for an involution. -/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Langlands.Global
open scoped ENNReal NNReal

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

variable {H : Type*} [Group H] (Γ : Subgroup H)

/-- `α⁻¹` also carries `Γ` onto itself. -/
theorem symm_mem_iff (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (x : H) :
    α.symm x ∈ Γ ↔ x ∈ Γ := by
  simpa using (hα (α.symm x)).symm

/-- The map `Γ x ↦ Γ α(x)` of `Γ \ H` induced by an automorphism with `α(Γ) = Γ`. -/
def cosetMap (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) :
    LeftCosetSpace Γ → LeftCosetSpace Γ :=
  LeftCosetSpace.lift Γ (fun x => LeftCosetSpace.mk Γ (α x)) fun γ x => by
    rw [map_mul]
    exact LeftCosetSpace.mk_subgroup_mul Γ ⟨α γ, (hα γ).2 γ.2⟩ (α x)

@[simp]
theorem cosetMap_mk (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (x : H) :
    cosetMap Γ α hα (LeftCosetSpace.mk Γ x) = LeftCosetSpace.mk Γ (α x) := rfl

theorem cosetMap_symm_cosetMap (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (q : LeftCosetSpace Γ) :
    cosetMap Γ α.symm (symm_mem_iff Γ α hα) (cosetMap Γ α hα q) = q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  simp

theorem cosetMap_cosetMap_symm (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (q : LeftCosetSpace Γ) :
    cosetMap Γ α hα (cosetMap Γ α.symm (symm_mem_iff Γ α hα) q) = q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  simp

section Measurable

variable [MeasurableSpace H]

theorem measurable_cosetMap (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (hm : Measurable α) :
    Measurable (cosetMap Γ α hα) :=
  measurable_from_quotient.mpr ((LeftCosetSpace.measurable_mk Γ).comp hm)

/-- The induced map as a measurable equivalence of `Γ \ H`. -/
def cosetMeasurableEquiv (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (hm : Measurable α)
    (hm' : Measurable α.symm) : LeftCosetSpace Γ ≃ᵐ LeftCosetSpace Γ where
  toFun := cosetMap Γ α hα
  invFun := cosetMap Γ α.symm (symm_mem_iff Γ α hα)
  left_inv := cosetMap_symm_cosetMap Γ α hα
  right_inv := cosetMap_cosetMap_symm Γ α hα
  measurable_toFun := measurable_cosetMap Γ α hα hm
  measurable_invFun := measurable_cosetMap Γ α.symm (symm_mem_iff Γ α hα) hm'

@[simp]
theorem coe_cosetMeasurableEquiv (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (hm : Measurable α) (hm' : Measurable α.symm) :
    ⇑(cosetMeasurableEquiv Γ α hα hm hm') = cosetMap Γ α hα := rfl

/-- **Transport of quotient measures.** The induced map pushes the quotient of `ν|_s` to the
quotient of `(α_* ν)|_{α(s)}`. -/
theorem map_cosetMap_quotientMeasure (α : H ≃* H) (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ)
    (hm : Measurable α) (hm' : Measurable α.symm) (ν : Measure H) (s : Set H) :
    Measure.map (cosetMap Γ α hα) (LeftCosetSpace.quotientMeasure Γ ν s) =
      LeftCosetSpace.quotientMeasure Γ (Measure.map α ν) (α.symm ⁻¹' s) := by
  let e : H ≃ᵐ H := ⟨α.toEquiv, hm, hm'⟩
  have he : ⇑e = ⇑α := rfl
  have hcomp : cosetMap Γ α hα ∘ LeftCosetSpace.mk Γ = LeftCosetSpace.mk Γ ∘ ⇑e := rfl
  rw [LeftCosetSpace.quotientMeasure, LeftCosetSpace.quotientMeasure,
    Measure.map_map (measurable_cosetMap Γ α hα hm) (LeftCosetSpace.measurable_mk Γ), hcomp,
    ← Measure.map_map (LeftCosetSpace.measurable_mk Γ) e.measurable, ← he,
    e.restrict_map]
  congr 2
  rw [he, show ⇑α ⁻¹' (⇑α.symm ⁻¹' s) = s by ext x; simp]

end Measurable

section Discrete

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

/-- The image of the chosen Borel fundamental domain under `α` is again a strict
fundamental domain for the left action of `Γ`. -/
theorem isFundamentalDomain_preimage_symm (hΓ : IsDiscrete (Γ : Set H)) (α : H ≃* H)
    (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (hm' : Measurable α.symm) (ν : Measure H) :
    IsFundamentalDomain Γ (α.symm ⁻¹' LeftCosetSpace.fundamentalDomain Γ hΓ) ν := by
  refine IsFundamentalDomain.mk'
    ((LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ).preimage hm').nullMeasurableSet
    fun x => ?_
  obtain ⟨δ, hδ, huniq⟩ := LeftCosetSpace.fundamentalDomain_unique Γ hΓ (α.symm x)
  refine ⟨⟨α δ, (hα δ).2 δ.2⟩, ?_, fun γ hγ => ?_⟩
  · show α.symm (α δ * x) ∈ LeftCosetSpace.fundamentalDomain Γ hΓ
    simpa using hδ
  · have hγ' : α.symm ((γ : H) * x) ∈ LeftCosetSpace.fundamentalDomain Γ hΓ := hγ
    rw [map_mul] at hγ'
    have := huniq ⟨α.symm γ, (symm_mem_iff Γ α hα γ).2 γ.2⟩ hγ'
    apply Subtype.ext
    change (γ : H) = α δ
    rw [← this]
    simp

/-- **Scaling of the discrete quotient measure.** If `α_* ν = c ν`, the induced map scales
the fundamental-domain quotient measure of `ν` by `c`. -/
theorem map_cosetMap_discreteQuotientMeasure (hΓ : IsDiscrete (Γ : Set H)) (α : H ≃* H)
    (hα : ∀ x, α x ∈ Γ ↔ x ∈ Γ) (hm : Measurable α) (hm' : Measurable α.symm)
    (ν : Measure H) [SMulInvariantMeasure Γ H ν] (c : ℝ≥0∞)
    (hc : Measure.map α ν = c • ν) :
    Measure.map (cosetMap Γ α hα) (LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν) =
      c • LeftCosetSpace.discreteQuotientMeasure Γ hΓ ν := by
  rw [LeftCosetSpace.discreteQuotientMeasure, map_cosetMap_quotientMeasure Γ α hα hm hm', hc,
    LeftCosetSpace.quotientMeasure_smul,
    ← LeftCosetSpace.discreteQuotientMeasure_eq Γ hΓ ν
      (isFundamentalDomain_preimage_symm Γ hΓ α hα hm' ν),
    LeftCosetSpace.discreteQuotientMeasure]

end Discrete

/-- **Normalized measures are preserved.** If a measurable bijection `f` of a measurable space
scales a measure `μ` by some factor, it preserves `(μ univ)⁻¹ • μ`. -/
theorem map_inv_measure_univ_smul {Q : Type*} [MeasurableSpace Q] (f : Q ≃ᵐ Q)
    (μ : Measure Q) (c : ℝ≥0∞) (hc : Measure.map f μ = c • μ) :
    Measure.map f ((μ univ)⁻¹ • μ) = (μ univ)⁻¹ • μ := by
  rw [Measure.map_smul _ f.measurable.aemeasurable, hc]
  have huniv : μ univ = c * μ univ := by
    have h := congrArg (fun ν : Measure Q => ν univ) hc
    simp only [Measure.smul_apply, smul_eq_mul] at h
    rwa [Measure.map_apply f.measurable MeasurableSet.univ, preimage_univ] at h
  by_cases h0 : μ univ = 0
  · rw [Measure.measure_univ_eq_zero.mp h0]
    simp
  by_cases htop : μ univ = ∞
  · rw [htop]
    simp
  have hc1 : c = 1 := by
    have h1 : 1 * μ univ = c * μ univ := by rw [one_mul]; exact huniv
    exact ((ENNReal.mul_left_inj h0 htop).mp h1).symm
  rw [hc1, one_smul]

section Haar

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- A topological automorphism scales Haar measure by the inverse of its Haar character. -/
theorem map_haar_eq_smul (φ : G ≃ₜ* G) :
    Measure.map φ (Measure.haar : Measure G) =
      ((mulEquivHaarChar φ : ℝ≥0∞))⁻¹ • (Measure.haar : Measure G) := by
  have h := mulEquivHaarChar_smul_map (Measure.haar : Measure G) φ
  have hpos : (mulEquivHaarChar φ : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (mulEquivHaarChar_pos φ).ne'
  calc Measure.map φ (Measure.haar : Measure G)
      = ((mulEquivHaarChar φ : ℝ≥0∞))⁻¹ • ((mulEquivHaarChar φ : ℝ≥0∞) •
          Measure.map φ (Measure.haar : Measure G)) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hpos ENNReal.coe_ne_top, one_smul]
    _ = _ := by
        congr 1

end Haar

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
