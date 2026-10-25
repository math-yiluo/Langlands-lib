import Langlands.Representation.CompactCoefficient.IsotypicSemisimplicityStatement

/-!
# Semisimplicity of intrinsic compact-isotypic sums

The proof transfers actual subrepresentations to monoid-algebra submodules,
then uses semisimplicity of images and arbitrary sums.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

universe uG uC uV

section Algebra

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- Semisimplicity of an actual subrepresentation agrees with semisimplicity
of the corresponding submodule of the ambient monoid-algebra module. -/
theorem isSemisimpleRepresentation_subrepresentation_iff (S : Subrepresentation ρ) :
    Representation.IsSemisimpleRepresentation S.toRepresentation ↔
      IsSemisimpleModule (MonoidAlgebra k G) S.asSubmodule := by
  let i : S.toRepresentation.IntertwiningMap ρ :=
    S.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let j : S.toRepresentation.asModule →ₗ[MonoidAlgebra k G] S.asSubmodule :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ i).codRestrict
      S.asSubmodule (fun v => v.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact j.isSemisimpleModule_iff_of_bijective hj

/-- An arbitrary supremum of semisimple subrepresentations is semisimple. -/
theorem isSemisimpleRepresentation_iSup {ι : Type*}
    (S : ι → Subrepresentation ρ)
    (hS : ∀ i, Representation.IsSemisimpleRepresentation (S i).toRepresentation) :
    Representation.IsSemisimpleRepresentation (⨆ i, S i).toRepresentation := by
  rw [isSemisimpleRepresentation_subrepresentation_iff]
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  change IsSemisimpleModule (MonoidAlgebra k G) (e (⨆ i, S i))
  rw [e.map_iSup]
  have h := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
    (s := Set.univ) (p := fun i => e (S i))
    (fun i _ => (isSemisimpleRepresentation_subrepresentation_iff (S i)).mp (hS i))
  have heq : (⨆ i ∈ (Set.univ : Set ι), e (S i)) = ⨆ i, e (S i) := by simp
  rw [heq] at h
  exact h

/-- The image of an intertwiner from a semisimple representation is semisimple. -/
theorem isSemisimpleRepresentation_range
    (hρ : Representation.IsSemisimpleRepresentation ρ) (f : ρ.IntertwiningMap σ) :
    Representation.IsSemisimpleRepresentation f.range.toRepresentation := by
  rw [isSemisimpleRepresentation_subrepresentation_iff]
  have : IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hρ
  let F := Representation.IntertwiningMap.equivLinearMapAsModule _ _ f
  have hF : f.range.asSubmodule = LinearMap.range F := by
    ext v
    rfl
  rw [hF]
  exact IsSemisimpleModule.range F

end Algebra

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Each intrinsic compact-isotypic part is semisimple, purely algebraically. -/
theorem isSemisimpleRepresentation_isotypicSubrepresentation
    (c : CompactCoefficientClass.{uG, uC} G) (A : SmoothRep.{0, uG, uV} ℂ G) :
    Representation.IsSemisimpleRepresentation (isotypicSubrepresentation c A).toRepresentation := by
  obtain ⟨D, hD⟩ := Quotient.exists_rep c
  change ofRep D = c at hD
  rw [isotypicSubrepresentation_eq_iSup_range D hD]
  apply isSemisimpleRepresentation_iSup
  intro f
  apply isSemisimpleRepresentation_range
  have : Representation.IsIrreducible D.obj.representation := D.property.1
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  infer_instance

/-- All three intrinsic compact-isotypic sums in the published statement
are semisimple, with independent group, representative, and ambient universes. -/
theorem isotypicSemisimplicityTheorem : IsotypicSemisimplicityTheorem.{uG, uC, uV} := by
  intro G _ _ A
  refine ⟨fun c => isSemisimpleRepresentation_isotypicSubrepresentation c A, ?_, ?_⟩
  · intro t
    exact isSemisimpleRepresentation_iSup _ fun c =>
      isSemisimpleRepresentation_isotypicSubrepresentation c.val A
  · exact isSemisimpleRepresentation_iSup _ fun c =>
      isSemisimpleRepresentation_isotypicSubrepresentation c A

end Langlands.CompactCoefficientClass
