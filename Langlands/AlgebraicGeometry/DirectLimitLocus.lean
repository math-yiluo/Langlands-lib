import Langlands.AlgebraicGeometry.ConstructibleAffineLimit

/-! # Full loci along a direct limit of rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Set Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry

/-- The actual cone of spectra attached to a ring cocone. -/
def specLimitCone {ι : Type u} [Category.{u} ι]
    {A : ι ⥤ CommRingCat.{u}} (c : Cocone A) : Cone (A.op ⋙ Scheme.Spec) :=
  Scheme.Spec.mapCone c.op

/-- Spectrum carries the given ring colimit to a scheme limit. -/
def isLimit_specLimitCone {ι : Type u} [Category.{u} ι]
    {A : ι ⥤ CommRingCat.{u}} (c : Cocone A) (hc : IsColimit c) :
    IsLimit (specLimitCone c) :=
  isLimitOfPreserves Scheme.Spec hc.op

private theorem spec_preimage_univ_of_later
    {ι : Type u} [Preorder ι] (A : ι ⥤ CommRingCat.{u})
    {i₀ i₁ i : ι} (h₁ : i₀ ≤ i₁) (h : i₀ ≤ i) (h₂ : i₁ ≤ i)
    (s : Set (Spec (A.obj i₀)))
    (hs : (Spec.map (A.map (homOfLE h₁))) ⁻¹' s = univ) :
    (Spec.map (A.map (homOfLE h))) ⁻¹' s = univ := by
  have e : Spec.map (A.map (homOfLE h)) =
      Spec.map (A.map (homOfLE h₂)) ≫ Spec.map (A.map (homOfLE h₁)) := by
    rw [← Spec.map_comp, ← A.map_comp]
    rfl
  apply eq_univ_of_forall
  intro x
  have hx := eq_univ_iff_forall.mp hs (Spec.map (A.map (homOfLE h₂)) x)
  simpa only [mem_preimage, e, Scheme.Hom.comp_apply] using hx

private theorem spec_preimage_univ_iff_eventually_of_detection
    {ι : Type u} [Preorder ι] (A : ι ⥤ CommRingCat.{u}) (c : Cocone A)
    (i₀ : ι) (s : Set (Spec (A.obj i₀)))
    (detect : (Spec.map (c.ι.app i₀)) ⁻¹' s = univ →
      ∃ (i₁ : ι) (h₁ : i₀ ≤ i₁),
        (Spec.map (A.map (homOfLE h₁))) ⁻¹' s = univ) :
    (Spec.map (c.ι.app i₀)) ⁻¹' s = univ ↔
      ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i →
        (Spec.map (A.map (homOfLE h))) ⁻¹' s = univ := by
  constructor
  · intro hs
    obtain ⟨i₁, h₁, hs₁⟩ := detect hs
    exact ⟨i₁, h₁, fun _ h h₂ => spec_preimage_univ_of_later A h₁ h h₂ s hs₁⟩
  · rintro ⟨i₁, h₁, hs₁⟩
    have hs := hs₁ i₁ h₁ le_rfl
    have e : Spec.map (c.ι.app i₀) =
        Spec.map (c.ι.app i₁) ≫ Spec.map (A.map (homOfLE h₁)) := by
      rw [← Spec.map_comp, c.w (homOfLE h₁)]
    apply eq_univ_of_forall
    intro x
    have hx := eq_univ_iff_forall.mp hs (Spec.map (c.ι.app i₁) x)
    simpa only [mem_preimage, e, Scheme.Hom.comp_apply] using hx

/-- An open locus over a stage is full at the ring colimit exactly when its
pullbacks are full at all sufficiently large stages. -/
theorem spec_preimage_eq_univ_iff_eventually_of_isOpen
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A : ι ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : ι) (s : Set (Spec (A.obj i₀))) (hs : IsOpen s) :
    (Spec.map (c.ι.app i₀)) ⁻¹' s = univ ↔
      ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i →
        (Spec.map (A.map (homOfLE h))) ⁻¹' s = univ := by
  apply spec_preimage_univ_iff_eventually_of_detection A c i₀ s
  intro H
  let : Nonempty ι := ⟨i₀⟩
  let D : ιᵒᵖ ⥤ Scheme.{u} := A.op ⋙ Scheme.Spec
  let d : Cone D := specLimitCone c
  have hd : IsLimit d := isLimit_specLimitCone c hc
  let (i : ιᵒᵖ) : IsAffine (D.obj i) := by dsimp [D]; infer_instance
  let {i j : ιᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) := by
    dsimp [D]
    infer_instance
  obtain ⟨j, f, hj⟩ := exists_map_eq_top D d hd (i := Opposite.op i₀) ⟨s, hs⟩
    (by apply SetLike.coe_injective; exact H)
  refine ⟨j.unop, leOfHom f.unop, ?_⟩
  exact congrArg (fun U : (D.obj j).Opens => (U : Set (D.obj j))) hj

/-- A constructible locus over a stage is full at the ring colimit exactly
when its pullbacks are full at all sufficiently large stages. -/
theorem spec_preimage_eq_univ_iff_eventually_of_isConstructible
    {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]
    (A : ι ⥤ CommRingCat.{u}) (c : Cocone A) (hc : IsColimit c)
    (i₀ : ι) (s : Set (Spec (A.obj i₀))) (hs : IsConstructible s) :
    (Spec.map (c.ι.app i₀)) ⁻¹' s = univ ↔
      ∃ i₁ : ι, i₀ ≤ i₁ ∧ ∀ (i : ι) (h : i₀ ≤ i), i₁ ≤ i →
        (Spec.map (A.map (homOfLE h))) ⁻¹' s = univ := by
  apply spec_preimage_univ_iff_eventually_of_detection A c i₀ s
  intro H
  let : Nonempty ι := ⟨i₀⟩
  let D : ιᵒᵖ ⥤ Scheme.{u} := A.op ⋙ Scheme.Spec
  let d : Cone D := specLimitCone c
  have hd : IsLimit d := isLimit_specLimitCone c hc
  let (i : ιᵒᵖ) : IsAffine (D.obj i) := by dsimp [D]; infer_instance
  let {i j : ιᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) := by
    dsimp [D]
    infer_instance
  obtain ⟨j, f, hj⟩ := SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible
    D d hd (Opposite.op i₀) s hs H
  exact ⟨j.unop, leOfHom f.unop, hj⟩

end Langlands.AlgebraicGeometry
