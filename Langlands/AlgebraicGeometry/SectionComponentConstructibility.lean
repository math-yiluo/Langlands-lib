import Langlands.AlgebraicGeometry.SectionComponentGenericClosure
import Langlands.AlgebraicGeometry.SectionComponentBaseChange
import Langlands.AlgebraicGeometry.SectionComponentLocality

/-! # Noetherian constructibility of section-selected components -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

/-- Constructible pieces over a nonempty open part of every irreducible closed target
subset suffice for constructibility of the entire source subset. -/
theorem isConstructible_of_noetherian_target_slices
    {A : Type v} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
    [NoetherianSpace B] (f : A → B) (S : Set A)
    (h : ∀ Z : Set B, IsClosed Z → IsIrreducible Z →
      ∃ U : Set B, IsOpen U ∧ (Z ∩ U).Nonempty ∧
        IsConstructible (f ⁻¹' (Z ∩ U) ∩ S)) : IsConstructible S := by
  classical
  have hind (Z : TopologicalSpace.Closeds B) : IsConstructible (f ⁻¹' (Z : Set B) ∩ S) := by
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih
    rcases eq_or_ne Z ⊥ with rfl | hne
    · simp
    · by_cases hirr : IsPreirreducible (Z : Set B)
      · obtain ⟨U, hU, hnonempty, hslice⟩ :=
          h Z Z.isClosed ⟨TopologicalSpace.Closeds.coe_nonempty.mpr hne, hirr⟩
        let W : TopologicalSpace.Closeds B := ⟨(Z : Set B) \ U, Z.isClosed.sdiff hU⟩
        have hlt : W < Z := by
          refine lt_iff_le_not_ge.mpr ⟨Set.sdiff_subset, ?_⟩
          intro hZW
          obtain ⟨y, hyZ, hyU⟩ := hnonempty
          exact (hZW hyZ).2 hyU
        have heq : f ⁻¹' (Z : Set B) ∩ S =
            (f ⁻¹' (W : Set B) ∩ S) ∪ (f ⁻¹' ((Z : Set B) ∩ U) ∩ S) := by
          ext x
          change (f x ∈ (Z : Set B) ∧ x ∈ S) ↔
            ((f x ∈ (Z : Set B) ∧ f x ∉ U) ∧ x ∈ S) ∨
              ((f x ∈ (Z : Set B) ∧ f x ∈ U) ∧ x ∈ S)
          tauto
        rw [heq]
        exact (ih W hlt).union hslice
      · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hirr
        obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hcover, hnot₁, hnot₂⟩ := hirr
        lift Z₁ to TopologicalSpace.Closeds B using hZ₁
        lift Z₂ to TopologicalSpace.Closeds B using hZ₂
        have h₁ := ih (Z ⊓ Z₁) (inf_lt_left.mpr hnot₁)
        have h₂ := ih (Z ⊓ Z₂) (inf_lt_left.mpr hnot₂)
        have heq : f ⁻¹' (Z : Set B) ∩ S =
            (f ⁻¹' ((Z ⊓ Z₁ : TopologicalSpace.Closeds B) : Set B) ∩ S) ∪
              (f ⁻¹' ((Z ⊓ Z₂ : TopologicalSpace.Closeds B) : Set B) ∩ S) := by
          ext x
          change (f x ∈ (Z : Set B) ∧ x ∈ S) ↔
            ((f x ∈ (Z : Set B) ∧ f x ∈ (Z₁ : Set B)) ∧ x ∈ S) ∨
              ((f x ∈ (Z : Set B) ∧ f x ∈ (Z₂ : Set B)) ∧ x ∈ S)
          constructor
          · rintro ⟨hxZ, hxS⟩
            rcases hcover hxZ with hx₁ | hx₂
            · exact Or.inl ⟨⟨hxZ, hx₁⟩, hxS⟩
            · exact Or.inr ⟨⟨hxZ, hx₂⟩, hxS⟩
          · rintro (⟨⟨hxZ, _⟩, hxS⟩ | ⟨⟨hxZ, _⟩, hxS⟩)
            all_goals exact ⟨hxZ, hxS⟩
        rw [heq]
        exact h₁.union h₂
  simpa using hind ⊤

/-- Constructibility of the actual component union for finite-type families over a
Noetherian base, with their actual sections. -/
def NoetherianComponentConstructibilityStatement : Prop :=
  ∀ (X Y : Scheme.{u}) [IsNoetherian Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y), IsConstructible (componentSet f e he)

/-- Generic geometric-connectedness constancy proves the Noetherian component
constructibility assertion by induction on closed subsets of the base. -/
theorem noetherianComponentConstructibility_of_genericConstancy
    (H : SchemeFiberGeometry.NoetherianGeometricallyConnectedFiberGenericConstancy.{u}) :
    NoetherianComponentConstructibilityStatement.{u} := by
  intro X Y _ f _ _ e he
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  apply isConstructible_of_noetherian_target_slices f (componentSet f e he)
  intro Z hZ hirr
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨Z, hZ⟩ : TopologicalSpace.Closeds Y)
  let b := I.subschemeι
  have hrange : Set.range b = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  let : IsNoetherian I.subscheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian b
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace b }
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace Z
    exact isIrreducible_iff_irreducibleSpace.mp hirr
  let f' := pullback.snd f b
  let a := pullback.fst f b
  let e' := baseChangeSection f e he b
  have he' : e' ≫ f' = 𝟙 _ := baseChangeSection_snd f e he b
  let : IsNoetherian (pullback f b : Scheme.{u}) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f'
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f' }
  let η := genericPoint I.subscheme
  obtain ⟨W, hW, hηW, heqW⟩ :=
    exists_open_componentClosure_eq_componentSet H f' e' he' (genericPoint_spec I.subscheme)
  obtain ⟨U, hU, himage⟩ := b.isEmbedding.isInducing.image_eq_isOpen_inter_range hW
  have himage' : b '' W = Z ∩ U := by
    simpa only [hrange, Set.inter_comm] using himage
  have hcomp : a ⁻¹' componentSet f e he = componentSet f' e' he' :=
    preimage_componentSet_of_isPullback_locallyOfFiniteType
      (IsPullback.of_hasPullback f b) (baseChangeSection_fst f e he b)
  have hconstructible : IsConstructible (f' ⁻¹' W ∩ componentSet f' e' he') := by
    rw [heqW]
    apply IsConstructible.inter
    · exact (NoetherianSpace.isCompact _).isConstructible (hW.preimage f'.continuous)
    · exact ((NoetherianSpace.isCompact _).isConstructible
        (componentClosure f' e' he' η).isClosed.isOpen_compl).of_compl
  have hsource : a '' (f' ⁻¹' W) = f ⁻¹' (b '' W) :=
    Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback f b).flip W
  have hslices : a '' (f' ⁻¹' W ∩ componentSet f' e' he') =
      f ⁻¹' (Z ∩ U) ∩ componentSet f e he := by
    rw [← hcomp, Set.image_inter_preimage, hsource, himage']
  refine ⟨U, hU, ?_, ?_⟩
  · exact ⟨b η, himage' ▸ Set.mem_image_of_mem b hηW⟩
  · rw [← hslices]
    exact a.isConstructible_image hconstructible

end Langlands.AlgebraicGeometry.SectionComponent
