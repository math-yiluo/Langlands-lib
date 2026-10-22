import Langlands.Weil.Local.RepresentationStatements
import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Representation.ContinuityProof
import Langlands.Weil.Representation.ContinuityBridgeProof

/-! # Continuity and character inertia for the actual local Weil group -/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Actual inertia is nonarchimedean with its induced subgroup topology. -/
theorem localInertia_nonarchimedean : NonarchimedeanGroup (localInertia F) := by
  let := localWeilGroup_nonarchimedean F
  refine { is_nonarchimedean := ?_ }
  intro U hU
  rw [nhds_subtype_eq_comap] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨K, hKV⟩ := NonarchimedeanGroup.is_nonarchimedean V hV
  refine ⟨K.comap (localInertia F).subtype continuous_subtype_val, ?_⟩
  exact (Set.preimage_mono hKV).trans hVU

/-- The full five-clause continuity criterion on the actual local Weil group. -/
theorem localWeilContinuity : LocalWeilContinuityFor.{u, v} F := by
  let I : OpenSubgroup (localWeilGroup F) :=
    ⟨localInertia F, localInertia_isOpen F⟩
  let : NonarchimedeanGroup I := localInertia_nonarchimedean F
  let : CompactSpace I := isCompact_iff_compactSpace.mp (localInertia_isCompact F)
  intro A
  exact (bundledRepresentationContinuity_iff.mpr representationContinuity)
    (localWeilGroup F) I A

/-- A continuous complex character has open kernel and finite image on actual inertia. -/
theorem localCharacterInertia : LocalCharacterInertiaFor.{u} F := by
  intro χ
  let ρ := Langlands.characterRepresentation χ.toMonoidHom
  have hc : Continuous (fun g => (ρ g).toContinuousLinearMap) := by
    apply continuous_clm_apply.mpr
    intro z
    exact (Units.continuous_val.comp χ.continuous).mul continuous_const
  let := localWeilGroup_nonarchimedean F
  have ho := open_kernel_of_continuous_nonarchimedean_representation ρ hc
  have hk : ρ.ker = χ.toMonoidHom.ker := by
    ext g
    change ρ g = 1 ↔ χ g = 1
    constructor
    · intro h
      apply Units.ext
      have he := congrArg (fun T : Module.End ℂ ℂ => T 1) h
      simpa [ρ, Langlands.characterRepresentation, Langlands.twist] using he
    · intro h
      ext
      simp [ρ, Langlands.characterRepresentation, Langlands.twist, h]
  rw [hk] at ho
  have hi : IsOpen ((χ.toMonoidHom.comp (localInertia F).subtype).ker :
      Set (localInertia F)) := ho.preimage continuous_subtype_val
  let : CompactSpace (localInertia F) :=
    isCompact_iff_compactSpace.mp (localInertia_isCompact F)
  exact ⟨hi, finite_range_of_open_kernel _ hi⟩

-- Check the complete unapplied types, retaining all outer parameters and universes.
example : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p),
    LocalWeilContinuityFor.{u, v} F :=
  @localWeilContinuity.{u, v}

example : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p),
    LocalCharacterInertiaFor.{u} F :=
  @localCharacterInertia.{u}

end Langlands.Weil.Local
