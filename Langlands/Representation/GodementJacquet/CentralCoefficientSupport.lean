import Langlands.Representation.GodementJacquet.Zeta
import Mathlib.GroupTheory.Index
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Compact central covers for matrix coefficients -/

noncomputable section

namespace Langlands.GodementJacquet

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The union of central translates of a set. -/
def centralSaturation (K : Set G) : Set G :=
  {g | ∃ z : Subgroup.center G, ∃ k ∈ K, g = (z : G) * k}

/-- Scalar functions whose support is contained in central translates of a
compact set. This is a support condition, with no unitarity requirement. -/
def compactCentralSupportFunctions : Submodule ℂ (G → ℂ) where
  carrier := {f | ∃ K : Set G, IsCompact K ∧ Function.support f ⊆ centralSaturation K}
  zero_mem' := ⟨∅, isCompact_empty, by simp⟩
  add_mem' := by
    rintro f g ⟨K, hK, hf⟩ ⟨L, hL, hg⟩
    refine ⟨K ∪ L, hK.union hL, ?_⟩
    intro x hx
    rcases Function.support_add f g hx with h | h
    · obtain ⟨z, k, hk, he⟩ := hf h
      exact ⟨z, k, Or.inl hk, he⟩
    · obtain ⟨z, k, hk, he⟩ := hg h
      exact ⟨z, k, Or.inr hk, he⟩
  smul_mem' := by
    rintro c f ⟨K, hK, hf⟩
    refine ⟨K, hK, ?_⟩
    intro x hx
    apply hf
    intro hz
    apply hx
    change c • f x = 0
    rw [hz, smul_zero]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact coefficient support on a normal subgroup that has finite index
after adjoining the center gives a compact central cover upstairs. -/
theorem matrixCoefficient_mem_compactCentralSupportFunctions
    (ρ : Representation ℂ G V)
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ (z : Subgroup.center G) (v : V), ρ (z : G) v = (χ z : ℂ) • v)
    (H : Subgroup G) [H.Normal] [(H ⊔ Subgroup.center G).FiniteIndex]
    (ℓ : Module.Dual ℂ V)
    (hH : ∀ w : V, HasCompactSupport (matrixCoefficient (ρ.comp H.subtype) ℓ w))
    (v : V) : matrixCoefficient ρ ℓ v ∈ compactCentralSupportFunctions := by
  let N := H ⊔ Subgroup.center G
  let r : G ⧸ N → G := fun j => j.out
  let C : G ⧸ N → Set H := fun j =>
    tsupport (matrixCoefficient (ρ.comp H.subtype) ℓ (ρ (r j) v))
  let K : Set G := ⋃ j, (fun h : H => (h : G) * r j) '' C j
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro j
    exact (hH (ρ (r j) v)).image (continuous_subtype_val.mul continuous_const)
  refine ⟨K, hK, ?_⟩
  intro g hg
  let j : G ⧸ N := QuotientGroup.mk g
  obtain ⟨n0, hn0⟩ := QuotientGroup.mk_out_eq_mul N g
  have hn0' : r j = g * n0 := hn0
  have hmem : (n0 : G)⁻¹ ∈ N := N.inv_mem n0.2
  obtain ⟨h, hh, z, hz, hhz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  let h' : G := r j * h * (r j)⁻¹
  have hh' : h' ∈ H := Subgroup.Normal.conj_mem inferInstance h hh (r j)
  have hg' : g = h' * r j * z := by
    have : g = r j * (n0 : G)⁻¹ := by rw [hn0']; group
    rw [this, ← hhz]
    simp only [h']
    group
  have hg'' : g = z * (h' * r j) := hg'.trans (Subgroup.mem_center_iff.mp hz _)
  have he : matrixCoefficient ρ ℓ v g = (χ ⟨z, hz⟩ : ℂ) *
      matrixCoefficient (ρ.comp H.subtype) ℓ (ρ (r j) v) ⟨h', hh'⟩ := by
    change ℓ (ρ g v) = _
    rw [hg'', map_mul, Module.End.mul_apply, hχ ⟨z, hz⟩, map_smul]
    change (χ ⟨z, hz⟩ : ℂ) * ℓ (ρ (h' * r j) v) = _
    rw [map_mul, Module.End.mul_apply]
    rfl
  have hs : (⟨h', hh'⟩ : H) ∈ C j := by
    apply subset_tsupport
    intro he0
    exact hg (by rw [he, he0, mul_zero])
  refine ⟨⟨z, hz⟩, h' * r j, ?_, hg''⟩
  exact Set.mem_iUnion.mpr ⟨j, ⟨⟨h', hh'⟩, hs, rfl⟩⟩

/-- The same compact central cover condition holds for the entire span of
actual smooth-vector, smooth-dual matrix coefficients. -/
theorem biSmoothMatrixCoefficients_le_compactCentralSupportFunctions
    (ρ : Representation ℂ G V)
    (χ : Subgroup.center G →* ℂˣ)
    (hχ : ∀ (z : Subgroup.center G) (v : V), ρ (z : G) v = (χ z : ℂ) • v)
    (H : Subgroup G) [H.Normal] [(H ⊔ Subgroup.center G).FiniteIndex]
    (hH : ∀ (ℓ : SmoothDual ρ) (w : V), HasCompactSupport
      (matrixCoefficient (ρ.comp H.subtype) (smoothDualPairing ρ ℓ) w)) :
    biSmoothMatrixCoefficients ρ ≤ compactCentralSupportFunctions := by
  apply Submodule.span_le.mpr
  rintro f ⟨ℓ, v, rfl⟩
  exact matrixCoefficient_mem_compactCentralSupportFunctions ρ χ hχ H
    (smoothDualPairing ρ ℓ) (hH ℓ) v.val

end Langlands.GodementJacquet
