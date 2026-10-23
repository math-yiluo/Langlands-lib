import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Scalar integrals stabilized over compact open additive subgroups -/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Langlands.HarmonicAnalysis

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X]
variable {μ : Measure X} {f g : X → ℂ} {z w : ℂ}

/-- A scalar integral stabilizes if every compact open subgroup containing one
fixed compact open subgroup gives the same, genuinely integrable, truncation. -/
def HasStableIntegral (μ : Measure X) (f : X → ℂ) (z : ℂ) : Prop :=
  ∃ K : OpenAddSubgroup X, IsCompact (K : Set X) ∧
    ∀ L : OpenAddSubgroup X, IsCompact (L : Set X) → K ≤ L →
      IntegrableOn f (L : Set X) μ ∧ (∫ x in (L : Set X), f x ∂μ) = z

omit [MeasurableSpace X] in
/-- Two compact open additive subgroups have a compact open common upper bound. -/
theorem isCompact_sup_openAddSubgroup (K L : OpenAddSubgroup X)
    (hK : IsCompact (K : Set X)) (hL : IsCompact (L : Set X)) :
    IsCompact ((K ⊔ L : OpenAddSubgroup X) : Set X) := by
  change IsCompact ((K.toAddSubgroup ⊔ L.toAddSubgroup : AddSubgroup X) : Set X)
  rw [AddSubgroup.add_normal]
  exact hK.add hL

namespace HasStableIntegral

/-- Evaluate at the common upper bound of two stabilization thresholds. -/
theorem unique (hf : HasStableIntegral μ f z) (hg : HasStableIntegral μ f w) :
    z = w := by
  obtain ⟨K, hK, hf⟩ := hf
  obtain ⟨L, hL, hg⟩ := hg
  have hc := isCompact_sup_openAddSubgroup K L hK hL
  exact (hf (K ⊔ L) hc le_sup_left).2.symm.trans
    (hg (K ⊔ L) hc le_sup_right).2

omit [IsTopologicalAddGroup X] in
theorem zero (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X)) :
    HasStableIntegral μ (0 : X → ℂ) 0 := by
  obtain ⟨K, hK⟩ := hX
  refine ⟨K, hK, fun L _ _ => ?_⟩
  exact ⟨integrable_zero _ _ _, by simp⟩

theorem add (hf : HasStableIntegral μ f z) (hg : HasStableIntegral μ g w) :
    HasStableIntegral μ (f + g) (z + w) := by
  obtain ⟨K, hK, hf⟩ := hf
  obtain ⟨L, hL, hg⟩ := hg
  refine ⟨K ⊔ L, isCompact_sup_openAddSubgroup K L hK hL, ?_⟩
  intro M hM hKM
  obtain ⟨hfi, hfv⟩ := hf M hM (le_sup_left.trans hKM)
  obtain ⟨hgi, hgv⟩ := hg M hM (le_sup_right.trans hKM)
  refine ⟨hfi.add hgi, ?_⟩
  change (∫ x in (M : Set X), f x + g x ∂μ) = z + w
  rw [integral_add hfi hgi, hfv, hgv]

omit [IsTopologicalAddGroup X] in
theorem smul (hf : HasStableIntegral μ f z) (c : ℂ) :
    HasStableIntegral μ (c • f) (c • z) := by
  obtain ⟨K, hK, hf⟩ := hf
  refine ⟨K, hK, ?_⟩
  intro L hL hKL
  obtain ⟨hfi, hfv⟩ := hf L hL hKL
  refine ⟨hfi.smul c, ?_⟩
  change (∫ x in (L : Set X), c • f x ∂μ) = c • z
  rw [integral_smul, hfv]

omit [IsTopologicalAddGroup X] in
theorem congr (hf : HasStableIntegral μ f z) (hfg : ∀ x, f x = g x) :
    HasStableIntegral μ g z := by
  have h : f = g := funext hfg
  exact h ▸ hf

end HasStableIntegral

/-- The actual functions whose scalar integral stabilizes form a complex
submodule. Existence of one compact open subgroup supplies the zero function. -/
def stableIntegrableSubmodule (μ : Measure X)
    (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X)) :
    Submodule ℂ (X → ℂ) where
  carrier := {f | ∃ z, HasStableIntegral μ f z}
  zero_mem' := ⟨0, HasStableIntegral.zero hX⟩
  add_mem' := by
    rintro f g ⟨z, hf⟩ ⟨w, hg⟩
    exact ⟨z + w, hf.add hg⟩
  smul_mem' := by
    rintro c f ⟨z, hf⟩
    exact ⟨c • z, hf.smul c⟩

@[simp] theorem mem_stableIntegrableSubmodule
    (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X)) :
    f ∈ stableIntegrableSubmodule μ hX ↔ ∃ z, HasStableIntegral μ f z := Iff.rfl

/-- Choose the unique stabilized value only for a function with proved
stabilization. No value is assigned to arbitrary functions. -/
def stableIntegral (μ : Measure X)
    (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X)) :
    stableIntegrableSubmodule μ hX →ₗ[ℂ] ℂ where
  toFun f := f.property.choose
  map_add' f g := (f + g).property.choose_spec.unique
    (f.property.choose_spec.add g.property.choose_spec)
  map_smul' c f := (c • f).property.choose_spec.unique
    (f.property.choose_spec.smul c)

theorem hasStableIntegral_stableIntegral
    (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X))
    (f : stableIntegrableSubmodule μ hX) :
    HasStableIntegral μ f (stableIntegral μ hX f) :=
  f.property.choose_spec

theorem stableIntegral_eq
    (hX : ∃ K : OpenAddSubgroup X, IsCompact (K : Set X))
    (f : stableIntegrableSubmodule μ hX) (hf : HasStableIntegral μ f z) :
    stableIntegral μ hX f = z :=
  (hasStableIntegral_stableIntegral hX f).unique hf

end Langlands.HarmonicAnalysis
