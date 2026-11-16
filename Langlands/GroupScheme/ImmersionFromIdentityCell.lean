import Langlands.GroupScheme.DominantHomFlat
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Immersions from a closed inverse image of an identity neighbourhood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityCell

section Categorical

variable {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {H G D V : C} [GrpObj H] [GrpObj G]
    (f : H ⟶ G) [IsMonHom f] (i : D ⟶ H) (k : D ⟶ V) (j : V ⟶ G)

/-- The family of all left translates of a morphism into the target group. -/
def translate : H ⊗ V ⟶ G := (fst H V ≫ f) * (snd H V ≫ j)

/-- Translating a cartesian cell square by the whole source group preserves
the cartesian square. -/
theorem isPullback_translate [Mono k] (h : IsPullback i k f j) :
    IsPullback (fst H D * (snd H D ≫ i)) (𝟙 H ⊗ₘ k) f (translate f j) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · simp only [translate, MonObj.mul_comp, MonObj.comp_mul, Category.assoc,
      tensorHom_fst_assoc, tensorHom_snd_assoc, Category.id_comp]
    rw [← h.w]
  · intro T φ ψ _ hprod
    apply CartesianMonoidalCategory.hom_ext
    · have hh := congrArg (fun a => a ≫ fst H V) hprod
      simpa using hh
    · apply (cancel_mono k).mp
      have hh := congrArg (fun a => a ≫ snd H V) hprod
      simpa using hh
  · intro T b a hab
    let x := a ≫ fst H V
    let v := a ≫ snd H V
    have hx : (x⁻¹ * b) ≫ f = v ≫ j := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hab]
      simp only [translate, MonObj.comp_mul, ← Category.assoc]
      change (x ≫ f)⁻¹ * ((x ≫ f) * (v ≫ j)) = v ≫ j
      exact inv_mul_cancel_left _ _
    let d := h.lift (x⁻¹ * b) v hx
    refine ⟨lift x d, ?_, ?_⟩
    · simp only [MonObj.comp_mul, lift_fst, lift_snd_assoc, d, h.lift_fst]
      exact mul_inv_cancel_left _ _
    · apply CartesianMonoidalCategory.hom_ext
      · simp [x]
      · simp [d, v]

end Categorical

section Schemes

variable {S : Scheme.{u}} {H G : GroupScheme S} (f : H ⟶ G)
    {V : Over S} (j : V ⟶ G.X)

theorem smooth_translate [Smooth H.X.hom] [IsOpenImmersion j.left] :
    Smooth (translate f.hom.hom j).left := by
  have ht :
      translate f.hom.hom j =
        (𝟙 H.X ⊗ₘ j) ≫ (DominantHomFlat.shearLeft f.hom.hom).hom ≫ snd H.X G.X := by
    rw [DominantHomFlat.shearLeft_hom_snd, MonObj.comp_mul]
    simp [translate]
  have : IsOpenImmersion (𝟙 H.X ⊗ₘ j).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have : IsIso (DominantHomFlat.shearLeft f.hom.hom).hom.left :=
    (Over.forget S).map_isIso (DominantHomFlat.shearLeft f.hom.hom).hom
  rw [ht, Over.comp_left, Over.comp_left, Over.snd_left]
  infer_instance

/-- The open image of all source translates of the target cell. -/
def saturation [Smooth H.X.hom] [IsOpenImmersion j.left] : G.X.left.Opens :=
  have := smooth_translate f j
  ⟨Set.range (translate f.hom.hom j).left,
    (translate f.hom.hom j).left.isOpenMap.isOpen_range⟩

/-- If the target cell contains the identity section, its translates by the
source contain the image of the homomorphism. -/
theorem range_subset_saturation [Smooth H.X.hom] [IsOpenImmersion j.left]
    (e : 𝟙_ (Over S) ⟶ V) (he : e ≫ j = 1) :
    Set.range f.hom.hom.left ⊆ saturation f j := by
  let s : H.X ⟶ H.X ⊗ V := lift (𝟙 H.X) (toUnit H.X ≫ e)
  have hs : s ≫ translate f.hom.hom j = f.hom.hom := by
    simp [s, translate, MonObj.comp_mul, he]
  rintro _ ⟨x, rfl⟩
  refine ⟨s.left x, ?_⟩
  exact congrArg (fun a : H.X ⟶ G.X => a.left x) hs

/-- A monomorphism from a smooth group is an immersion if its inverse image
over an open identity neighbourhood is closed in that neighbourhood. -/
theorem isImmersion_of_isPullback [Smooth H.X.hom] [IsOpenImmersion j.left]
    [Mono f.hom.hom] {D : Over S} (i : D ⟶ H.X) (k : D ⟶ V)
    [IsClosedImmersion k.left] (h : IsPullback i k f.hom.hom j)
    (e : 𝟙_ (Over S) ⟶ V) (he : e ≫ j = 1) :
    IsImmersion f.hom.hom.left := by
  have : Mono k := Over.mono_of_mono_left k
  have ht := (isPullback_translate f.hom.hom i k j h).map (Over.forget S)
  change IsPullback (fst H.X D * (snd H.X D ≫ i)).left
    (𝟙 H.X ⊗ₘ k).left f.hom.hom.left (translate f.hom.hom j).left at ht
  have hprod : IsClosedImmersion (𝟙 H.X ⊗ₘ k).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      inferInstance inferInstance (Over.w _).symm (Over.w _).symm
  let W := saturation f j
  let a := translate f.hom.hom j
  let a' : (H.X ⊗ V).left ⟶ W :=
    IsOpenImmersion.lift W.ι a.left (by
      rw [Scheme.Opens.range_ι]
      exact Set.Subset.rfl)
  let f' : H.X.left ⟶ W :=
    IsOpenImmersion.lift W.ι f.hom.hom.left (by
      rw [Scheme.Opens.range_ι]
      exact range_subset_saturation f j e he)
  have ha : a' ≫ W.ι = a.left := IsOpenImmersion.lift_fac _ _ _
  have hf : f' ≫ W.ι = f.hom.hom.left := IsOpenImmersion.lift_fac _ _ _
  have hpa : IsPullback (𝟙 (H.X ⊗ V).left) a' a.left W.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using ha.symm⟩
  have : Smooth a' :=
    MorphismProperty.of_isPullback hpa (smooth_translate f j)
  have : Surjective a' := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, ?_⟩
    apply W.ι.injective
    exact (congrArg (fun b => b y) ha).trans hy
  have hsq : IsPullback (fst H.X D * (snd H.X D ≫ i)).left
      (𝟙 H.X ⊗ₘ k).left f' a' := by
    refine IsPullback.mk' ?_ ?_ ?_
    · apply (cancel_mono W.ι).mp
      simpa only [Category.assoc, hf, ha] using
        (show _ = (𝟙 H.X ⊗ₘ k).left ≫ a.left from ht.w)
    · intro T φ ψ h₁ h₂
      exact ht.hom_ext h₁ h₂
    · intro T b c hbc
      have hbc' : b ≫ f.hom.hom.left = c ≫ a.left := by
        rw [← hf, ← ha, ← Category.assoc, ← Category.assoc, hbc]
      exact ⟨ht.lift b c hbc', ht.lift_fst _ _ _, ht.lift_snd _ _ _⟩
  have : IsFinite f' :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsFinite)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hsq.flip
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : Mono f.hom.hom.left := (Over.forget S).map_mono f.hom.hom
  have : Mono (f' ≫ W.ι) := hf.symm ▸ inferInstance
  have : Mono f' := mono_of_mono f' W.ι
  have : IsClosedImmersion f' :=
    (IsClosedImmersion.iff_isFinite_and_mono f').mpr ⟨inferInstance, inferInstance⟩
  rw [← hf]
  infer_instance

end Schemes

end Langlands.GroupScheme.IdentityCell
