import Langlands.Geometry.Analytic.AtlasTopology.QuasinetProperties
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections
import Mathlib.Topology.LocallyConstant.Basic

/-! # Local constancy detected by quasinets -/

universe u v

namespace Langlands.Analytic.AtlasTopology

open Set

variable {X : Type u} [TopologicalSpace X] {A : Type v}

/-- Restrictions to all actual quasinet members detect local constancy,
without a topology or nonemptiness assumption on the coefficient type. -/
theorem IsQuasinet.isLocallyConstant_iff {τ : Set (Set X)}
    (hτ : IsQuasinet τ) (f : X → A) :
    IsLocallyConstant f ↔
      ∀ V ∈ τ, IsLocallyConstant (fun x : V => f x.val) := by
  constructor
  · intro hf V _
    exact hf.comp_continuous continuous_subtype_val
  · intro hf s
    exact (hτ.isOpen_iff (f ⁻¹' s)).mpr fun V hV => hf V hV s

/-- Finite relative local refinements detect local constancy on the
unchanged target subspace through the actual subset inclusions. -/
theorem LocallyRefines.isLocallyConstant_iff {τ : Set (Set X)} {S : Set X}
    (hτ : LocallyRefines τ {S}) (f : S → A) :
    IsLocallyConstant f ↔ ∀ V ∈ τ, ∀ hVS : V ⊆ S,
      IsLocallyConstant (fun x : V => f (Set.inclusion hVS x)) := by
  constructor
  · intro hf V _ hVS
    exact hf.comp_continuous (continuous_inclusion hVS)
  · intro hf
    apply (((isQuasinet_restrictedFamily_iff τ S).mpr hτ).isLocallyConstant_iff f).mpr
    rintro W ⟨V, hV, hVS, rfl⟩
    have hc : Continuous (fun x : (Subtype.val ⁻¹' V : Set S) =>
        (⟨x.val.val, x.property⟩ : V)) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (hf V hV hVS).comp_continuous hc

end Langlands.Analytic.AtlasTopology
