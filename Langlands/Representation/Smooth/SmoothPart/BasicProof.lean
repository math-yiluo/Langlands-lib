import Langlands.Representation.Smooth.SmoothPart.BasicStatement

/-! # Basic properties of the smooth part -/

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V]
variable {ρ : Representation R G V}

theorem isSmoothVector_zero : IsSmoothVector ρ 0 :=
  (smoothVectors ρ).zero_mem

theorem isSmoothVector_add {v w : V} (hv : IsSmoothVector ρ v)
    (hw : IsSmoothVector ρ w) : IsSmoothVector ρ (v + w) :=
  (smoothVectors ρ).add_mem hv hw

theorem isSmoothVector_smul (a : R) {v : V} (hv : IsSmoothVector ρ v) :
    IsSmoothVector ρ (a • v) :=
  (smoothVectors ρ).smul_mem a hv

theorem mem_smoothVectors_iff (v : V) :
    v ∈ smoothVectors ρ ↔ IsSmoothVector ρ v :=
  Iff.rfl

theorem isSmooth_iff_smoothVectors_eq_top :
    IsSmooth ρ ↔ smoothVectors ρ = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro v _
    exact h v
  · intro h v
    change v ∈ smoothVectors ρ
    rw [h]
    trivial

variable [IsTopologicalGroup G]

theorem isSmoothVector_apply (g : G) {v : V} (hv : IsSmoothVector ρ v) :
    IsSmoothVector ρ (ρ g v) :=
  (smoothSubrepresentation ρ).apply_mem_toSubmodule g hv

theorem smoothInclusion_apply (v : smoothVectors ρ) :
    smoothInclusion ρ v = (v : V) :=
  rfl

theorem smoothInclusion_injective :
    Function.Injective (smoothInclusion ρ) :=
  Subtype.val_injective

theorem isSmooth_smoothPart (ρ : Representation R G V) : IsSmooth (smoothPart ρ) := by
  intro v
  obtain ⟨K, hK⟩ := v.property
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

omit [IsTopologicalGroup G] in
theorem smoothPartBasic : SmoothPartBasicStatement (R := R) (G := G) (V := V) := by
  intro ρ
  refine ⟨fun v => mem_smoothVectors_iff v, isSmoothVector_zero,
    fun _ _ => isSmoothVector_add, fun a _ => isSmoothVector_smul a,
    isSmooth_iff_smoothVectors_eq_top, ?_⟩
  intro _
  exact ⟨fun g _ => isSmoothVector_apply g, isSmooth_smoothPart ρ,
    fun v => smoothInclusion_apply v, smoothInclusion_injective⟩

end Langlands
