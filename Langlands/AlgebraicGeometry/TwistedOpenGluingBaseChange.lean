import Langlands.AlgebraicGeometry.TwistedOpenGluing
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Twisted gluings over a base and their base change along closed immersions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.TwistedOpenGluing

/-- Restrictions of a morphism to opens commute with inclusions of opens. -/
@[reassoc]
theorem homOfLE_resLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens}
    (hU : U' ≤ U) (hV : V' ≤ V) (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') :
    X.homOfLE hV ≫ f.resLE U V e = f.resLE U' V' e' ≫ Y.homOfLE hU := by
  rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
    Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]

namespace Data

variable {C S : Scheme.{u}} (D : Data C) (π : C ⟶ S)

/-- The transition maps are morphisms over `S`. -/
def IsOver : Prop := ∀ i j, D.θ i j ≫ π = (D.V i ⊓ D.V j).ι ≫ π

variable {D π} (hπ : D.IsOver π)

include hπ in
theorem restrictTo_comp_over {i j : D.J} {W Q : C.Opens} (hW : W ≤ D.V i ⊓ D.V j) (hQ : W ≤ Q) :
    restrictTo (D.θ i j) (D.pointwise i j) hW hQ ≫ Q.ι ≫ π = W.ι ≫ π := by
  rw [restrictTo_ι_assoc, hπ, Scheme.homOfLE_ι_assoc]

/-- The structure morphism of the glued scheme. -/
def toBase : D.glued ⟶ S :=
  D.desc (fun i ↦ (D.V i).ι ≫ π) (fun i j ↦ by
    rw [Scheme.homOfLE_ι_assoc, D.restrictTo_comp_over hπ])

@[reassoc (attr := simp)]
theorem ι_toBase (i : D.J) : D.ι i ≫ D.toBase hπ = (D.V i).ι ≫ π :=
  D.ι_desc _ _ i

set_option backward.isDefEq.respectTransparency false in
theorem smooth_toBase [Smooth π] : Smooth (D.toBase hπ) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @Smooth) D.core.glueData.openCover fun i ↦ ?_
  change Smooth (D.ι i ≫ D.toBase hπ)
  rw [ι_toBase]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem locallyOfFiniteType_toBase [LocallyOfFiniteType π] :
    LocallyOfFiniteType (D.toBase hπ) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    D.core.glueData.openCover fun i ↦ ?_
  change LocallyOfFiniteType (D.ι i ≫ D.toBase hπ)
  rw [ι_toBase]
  infer_instance

section BaseChange

variable {T : Scheme.{u}} (t : T ⟶ S) [IsClosedImmersion t]

/-- The pieces pulled back to the base change of `C`. -/
abbrev VT (i : D.J) : (pullback π t).Opens := pullback.fst π t ⁻¹ᵁ D.V i

/-- The restriction of the projection to a pulled-back overlap. -/
abbrev ρ (i j : D.J) : (VT (D := D) (π := π) t i ⊓ VT t j).toScheme ⟶ (D.V i ⊓ D.V j).toScheme :=
  (pullback.fst π t).resLE (D.V i ⊓ D.V j) _ le_rfl

omit [IsClosedImmersion t] in
@[reassoc]
theorem ρ_ι (i j : D.J) :
    ρ t i j ≫ (D.V i ⊓ D.V j).ι = (VT (D := D) (π := π) t i ⊓ VT t j).ι ≫ pullback.fst π t :=
  Scheme.Hom.resLE_comp_ι _ _

omit [IsClosedImmersion t] in
include hπ in
theorem ρ_θ_π (i j : D.J) :
    ρ t i j ≫ D.θ i j ≫ π = (VT (D := D) (π := π) t i ⊓ VT t j).ι ≫ pullback.snd π t ≫ t := by
  rw [hπ, ρ_ι_assoc, pullback.condition]

/-- The pulled-back transition maps. -/
def θT (i j : D.J) : (VT (D := D) (π := π) t i ⊓ VT t j).toScheme ⟶ pullback π t :=
  pullback.lift (ρ t i j ≫ D.θ i j) ((VT t i ⊓ VT t j).ι ≫ pullback.snd π t)
    (by rw [Category.assoc, ρ_θ_π hπ, Category.assoc])

omit [IsClosedImmersion t] in
@[reassoc (attr := simp)]
theorem θT_fst (i j : D.J) : θT hπ t i j ≫ pullback.fst π t = ρ t i j ≫ D.θ i j :=
  pullback.lift_fst _ _ _

omit [IsClosedImmersion t] in
@[reassoc (attr := simp)]
theorem θT_snd (i j : D.J) :
    θT hπ t i j ≫ pullback.snd π t = (VT (D := D) (π := π) t i ⊓ VT t j).ι ≫ pullback.snd π t :=
  pullback.lift_snd _ _ _

theorem θT_pointwise (i j : D.J) : IsPointwiseInclusion (θT hπ t i j) := by
  intro x
  apply (pullback.fst π t).isClosedEmbedding.injective
  rw [← Scheme.Hom.comp_apply, θT_fst, Scheme.Hom.comp_apply, D.pointwise i j,
    ← Scheme.Hom.comp_apply, ρ_ι, Scheme.Hom.comp_apply]

omit [IsClosedImmersion t] in
theorem θT_self (i : D.J) : θT hπ t i i = (VT (D := D) (π := π) t i ⊓ VT t i).ι := by
  apply pullback.hom_ext
  · rw [θT_fst, D.self, ρ_ι]
  · rw [θT_snd]

theorem θT_cocycle (i j k : D.J) :
    restrictTo (θT hπ t j k) (θT_pointwise hπ t j k)
        (W := VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ θT hπ t i j =
      (pullback π t).homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k ≤ VT t i ⊓ VT t k) ≫ θT hπ t i k := by
  let ρW : (VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k).toScheme ⟶
      (D.V i ⊓ D.V j ⊓ D.V k).toScheme := (pullback.fst π t).resLE _ _ le_rfl
  have h₁ : restrictTo (θT hπ t j k) (θT_pointwise hπ t j k)
        (W := VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left ≫ ρ t i j =
      ρW ≫ restrictTo (D.θ j k) (D.pointwise j k) (W := D.V i ⊓ D.V j ⊓ D.V k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) inf_le_left := by
    have h₃ : (pullback π t).homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k ≤ VT t j ⊓ VT t k) ≫ ρ t j k =
        ρW ≫ C.homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          D.V i ⊓ D.V j ⊓ D.V k ≤ D.V j ⊓ D.V k) :=
      homOfLE_resLE _ _ _ _ _
    rw [← cancel_mono (D.V i ⊓ D.V j).ι, Category.assoc, ρ_ι, restrictTo_ι_assoc, θT_fst,
      Category.assoc, restrictTo_ι, reassoc_of% h₃]
  have h₂ : (pullback π t).homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          VT (D := D) (π := π) t i ⊓ VT t j ⊓ VT t k ≤ VT t i ⊓ VT t k) ≫ ρ t i k =
      ρW ≫ C.homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          D.V i ⊓ D.V j ⊓ D.V k ≤ D.V i ⊓ D.V k) :=
    homOfLE_resLE _ _ _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, θT_fst, reassoc_of% h₁, D.cocycle, Category.assoc, θT_fst,
      reassoc_of% h₂]
  · rw [Category.assoc, θT_snd, restrictTo_ι_assoc, θT_snd, Scheme.homOfLE_ι_assoc,
      Category.assoc, θT_snd, Scheme.homOfLE_ι_assoc]

/-- The gluing data pulled back along a closed immersion of the base. -/
def baseChange : Data (pullback π t) where
  J := D.J
  V := VT t
  θ := θT hπ t
  pointwise := θT_pointwise hπ t
  self := θT_self hπ t
  cocycle := θT_cocycle hπ t

/-- The projection of a pulled-back piece to the original piece. -/
abbrev r (i : D.J) : (VT (D := D) (π := π) t i).toScheme ⟶ (D.V i).toScheme :=
  pullback.fst π t ∣_ D.V i

/-- The base change of the open immersion of a piece into the glued scheme. -/
def κ (i : D.J) : (VT (D := D) (π := π) t i).toScheme ⟶ pullback (D.toBase hπ) t :=
  pullback.lift (r t i ≫ D.ι i) ((VT t i).ι ≫ pullback.snd π t) (by
    rw [Category.assoc, ι_toBase, morphismRestrict_ι_assoc, pullback.condition, Category.assoc])

omit [IsClosedImmersion t] in
@[reassoc (attr := simp)]
theorem κ_fst (i : D.J) : κ hπ t i ≫ pullback.fst (D.toBase hπ) t = r t i ≫ D.ι i :=
  pullback.lift_fst _ _ _

omit [IsClosedImmersion t] in
@[reassoc (attr := simp)]
theorem κ_snd (i : D.J) :
    κ hπ t i ≫ pullback.snd (D.toBase hπ) t = (VT (D := D) (π := π) t i).ι ≫ pullback.snd π t :=
  pullback.lift_snd _ _ _

omit [IsClosedImmersion t] in
theorem isPullback_κ (i : D.J) :
    IsPullback (r t i) (κ hπ t i) (D.ι i) (pullback.fst (D.toBase hπ) t) := by
  refine IsPullback.of_bot ?_ (κ_fst hπ t i).symm (IsPullback.of_hasPullback _ _)
  rw [κ_snd, ι_toBase]
  exact (isPullback_morphismRestrict (pullback.fst π t) (D.V i)).paste_vert
    (IsPullback.of_hasPullback π t)

instance isOpenImmersion_κ (i : D.J) : IsOpenImmersion (κ hπ t i) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_κ hπ t i) inferInstance

omit [IsClosedImmersion t] in
theorem opensRange_κ (i : D.J) :
    (κ hπ t i).opensRange = pullback.fst (D.toBase hπ) t ⁻¹ᵁ (D.ι i).opensRange := by
  have h := Scheme.Hom.opensRange_comp_of_isIso (isPullback_κ hπ t i).isoPullback.hom
    (pullback.snd (D.ι i) (pullback.fst (D.toBase hπ) t))
  simp only [IsPullback.isoPullback_hom_snd] at h
  rw [h, Scheme.Hom.opensRange_pullbackSnd]

theorem κ_compat (i j : D.J) :
    (pullback π t).homOfLE (inf_le_right : VT (D := D) (π := π) t i ⊓ VT t j ≤ VT t j) ≫
        κ hπ t j =
      restrictTo (θT hπ t i j) (θT_pointwise hπ t i j) le_rfl inf_le_left ≫ κ hπ t i := by
  have h₁ : (pullback π t).homOfLE (inf_le_right : VT (D := D) (π := π) t i ⊓ VT t j ≤ VT t j) ≫
      r t j = ρ t i j ≫ C.homOfLE (inf_le_right : D.V i ⊓ D.V j ≤ D.V j) := by
    rw [← cancel_mono (D.V j).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, ρ_ι]
  have h₂ : restrictTo (θT hπ t i j) (θT_pointwise hπ t i j) le_rfl inf_le_left ≫ r t i =
      ρ t i j ≫ restrictTo (D.θ i j) (D.pointwise i j) le_rfl inf_le_left := by
    rw [← cancel_mono (D.V i).ι, Category.assoc, morphismRestrict_ι, restrictTo_ι_assoc,
      Scheme.homOfLE_rfl, Category.id_comp, θT_fst, Category.assoc, restrictTo_ι,
      Scheme.homOfLE_rfl, Category.id_comp]
  apply pullback.hom_ext
  · rw [Category.assoc, κ_fst, reassoc_of% h₁, D.glue, Category.assoc, κ_fst, reassoc_of% h₂]
  · rw [Category.assoc, κ_snd, Scheme.homOfLE_ι_assoc, Category.assoc, κ_snd,
      restrictTo_ι_assoc, Scheme.homOfLE_rfl, Category.id_comp, θT_snd]

omit [IsClosedImmersion t] in
theorem κ_pre (i j : D.J) :
    (κ hπ t j) ⁻¹ᵁ (κ hπ t i).opensRange ≤ (VT (D := D) (π := π) t j).ι ⁻¹ᵁ VT t i := by
  intro x hx
  rw [opensRange_κ, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
    κ_fst, Scheme.Hom.comp_apply, ← Scheme.Hom.mem_preimage, preimage_opensRange] at hx
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
    ← morphismRestrict_ι, Scheme.Hom.comp_apply]
  exact hx

omit [IsClosedImmersion t] in
theorem κ_cover : ⨆ i, (κ hπ t i).opensRange = ⊤ := by
  simp_rw [opensRange_κ]
  exact Scheme.Hom.iSup_preimage_eq_top _ D.iSup_opensRange

/-- The glued scheme of the pulled-back data is the base change of the glued scheme. -/
def baseChangeIso : (D.baseChange hπ t).glued ≅ pullback (D.toBase hπ) t :=
  @Data.recognize _ (D.baseChange hπ t) _ (κ hπ t)
    (fun i ↦ isOpenImmersion_κ hπ t i) (κ_cover hπ t) (κ_pre hπ t)
    (κ_compat hπ t)

@[reassoc (attr := simp)]
theorem ι_baseChangeIso_hom (i : D.J) :
    (D.baseChange hπ t).ι i ≫ (D.baseChangeIso hπ t).hom = κ hπ t i :=
  @Data.ι_recognize_hom _ (D.baseChange hπ t) _ (κ hπ t)
    (fun i ↦ isOpenImmersion_κ hπ t i) (κ_cover hπ t) (κ_pre hπ t)
    (κ_compat hπ t) i

end BaseChange

end Data

end Langlands.AlgebraicGeometry.TwistedOpenGluing
