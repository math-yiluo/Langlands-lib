import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Analysis.Local.QuotientTopology

/-!
# Compact induction from locally constant covariant functions

Compact projected support turns pointwise local constancy into a single open
right stabilizer. The constructor retains the published compact-induction carrier.
-/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.Induction

universe uR uG uV

section Stabilizer

variable {G : Type uG} {V : Type uV} [Group G]

/-- The actual subgroup fixing the whole function under right translation. -/
def rightFunctionStabilizer (f : G → V) : Subgroup G where
  carrier := {g | ∀ x, f (x * g) = f x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb x
    rw [← mul_assoc, hb, ha]
  inv_mem' := by
    intro a ha x
    simpa using (ha (x * a⁻¹)).symm

@[simp]
theorem mem_rightFunctionStabilizer (f : G → V) (g : G) :
    g ∈ rightFunctionStabilizer f ↔ ∀ x, f (x * g) = f x :=
  Iff.rfl

variable [Zero V]

/-- Right translations fixing a function preserve its actual nonzero support. -/
theorem mul_mem_support_iff_of_mem_rightFunctionStabilizer
    (f : G → V) {g : G} (hg : g ∈ rightFunctionStabilizer f) (x : G) :
    x * g ∈ Function.support f ↔ x ∈ Function.support f := by
  simp only [Function.mem_support, hg x]

end Stabilizer

section Covariance

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- Covariance saturates the actual nonzero support under the subgroup. -/
theorem quotientMap_mem_quotientSupport_iff_of_covariant
    (H : Subgroup G) (σ : Representation R H V) (f : G → V)
    (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x)) (x : G) :
    quotientMap H x ∈ quotientSupport H f ↔ f x ≠ 0 := by
  constructor
  · rintro ⟨y, hy, hxy⟩ hx
    have hh : y * x⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
    have heq := hcov ⟨y * x⁻¹, hh⟩ x
    have hz : f y = 0 := by
      simpa [mul_assoc, hx] using heq
    exact hy hz
  · intro hx
    exact ⟨x, hx, rfl⟩

end Covariance

section Topology

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Local constancy gives one identity neighborhood preserving values on a compact set. -/
theorem exists_nhds_one_eq_on_isCompact (f : G → V) (hlc : IsLocallyConstant f)
    {C : Set G} (hC : IsCompact C) :
    ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ ∀ g ∈ U, ∀ c ∈ C, f (c * g) = f c := by
  have hevent : ∀ᶠ g in 𝓝 (1 : G), ∀ c ∈ C, f (c * g) = f c := by
    apply hC.eventually_forall_of_forall_eventually
    intro c _
    have hm := (hlc.comp_continuous (continuous_snd.mul continuous_fst)).eventually_eq
      (1, c)
    have hp := (hlc.comp_continuous continuous_snd).eventually_eq ((1 : G), c)
    filter_upwards [hm, hp] with p hmul hfst
    have hmul' : f (p.2 * p.1) = f c := by simpa using hmul
    exact hmul'.trans hfst.symm
  exact ⟨_, hevent, fun _ hg => hg⟩

end Topology

section Construction

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace G] [AddCommGroup V] [Module R V]

/-- A locally constant covariant function with compact projected support has open
actual right stabilizer. -/
theorem isOpen_rightFunctionStabilizer_of_isCompact_quotientSupport
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (σ : Representation R H V) (f : G → V)
    (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (hlc : IsLocallyConstant f) (hc : IsCompact (quotientSupport H f)) :
    IsOpen (rightFunctionStabilizer f : Set G) := by
  obtain ⟨C, hC, himage⟩ :=
    Langlands.QuotientIntegration.leftQuotient_exists_isCompact_image H hH hc
  obtain ⟨U, hU, hfix⟩ := exists_nhds_one_eq_on_isCompact f hlc hC
  have hnonzero : ∀ g ∈ U, ∀ x : G, f x ≠ 0 → f (x * g) = f x := by
    intro g hg x hx
    have hqx : quotientMap H x ∈ quotientSupport H f := ⟨x, hx, rfl⟩
    rw [← himage] at hqx
    obtain ⟨c, hcC, hcx⟩ := hqx
    have hh : x * c⁻¹ ∈ H :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact hcx)
    let h : H := ⟨x * c⁻¹, hh⟩
    have hxrep : (h : G) * c = x := by simp [h]
    calc
      f (x * g) = f ((h : G) * (c * g)) := by rw [← mul_assoc, hxrep]
      _ = σ h (f (c * g)) := hcov h _
      _ = σ h (f c) := by rw [hfix g hg c hcC]
      _ = f x := by rw [← hcov h c, hxrep]
  apply (rightFunctionStabilizer f).isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset (inter_mem hU (inv_mem_nhds_one G hU))
  intro g hg x
  by_cases hx : f x = 0
  · by_cases hxg : f (x * g) = 0
    · exact hxg.trans hx.symm
    · have heq := hnonzero g⁻¹ hg.2 (x * g) hxg
      simpa using heq.symm
  · exact hnonzero g hg.1 x hx

/-- The derived uniform open right stabilizer of the whole function. -/
def locallyConstantCompactOpenStabilizer
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (σ : Representation R H V) (f : G → V)
    (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (hlc : IsLocallyConstant f) (hc : IsCompact (quotientSupport H f)) :
    OpenSubgroup G :=
  ⟨rightFunctionStabilizer f,
    isOpen_rightFunctionStabilizer_of_isCompact_quotientSupport H hH σ f hcov hlc hc⟩

/-- Construct actual compact induction from covariance, local constancy and compact
projected nonzero support, deriving the uniform open stabilizer. -/
def compactFunctionOfLocallyConstant
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (σ : Representation R H V) (f : G → V)
    (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (hlc : IsLocallyConstant f) (hc : IsCompact (quotientSupport H f)) :
    CompactFunctions H σ :=
  compactFunctionOf H σ f hcov
    (locallyConstantCompactOpenStabilizer H hH σ f hcov hlc hc)
    (fun g x => g.property x) hc

@[simp]
theorem eval_compactFunctionOfLocallyConstant
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (σ : Representation R H V) (f : G → V)
    (hcov : ∀ (h : H) (x : G), f ((h : G) * x) = σ h (f x))
    (hlc : IsLocallyConstant f) (hc : IsCompact (quotientSupport H f)) (x : G) :
    eval H σ (compactFunctionOfLocallyConstant H hH σ f hcov hlc hc).1 x = f x :=
  rfl

end Construction

end Langlands.Induction
