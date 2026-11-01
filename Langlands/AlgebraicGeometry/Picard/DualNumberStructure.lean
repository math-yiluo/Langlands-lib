import Langlands.AlgebraicGeometry.Picard.DualNumberThickening
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Structure sections of the actual dual-number thickening -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.DualNumberThickening

open Langlands.GroupScheme.GeneralLinear.DualNumber

/-- Coefficientwise dual numbers as a functor on commutative rings. -/
def dualNumberFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj R := CommRingCat.of (DualNumber R)
  map f := CommRingCat.ofHom (coefficientMap f.hom)
  map_id R := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact TrivSqZeroExt.ext rfl rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact TrivSqZeroExt.ext rfl rfl

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k))

/-- The split dual-number presheaf on the original scheme. -/
def splitPresheaf : TopCat.Presheaf CommRingCat.{u} X :=
  X.presheaf ⋙ dualNumberFunctor

/-- Sections of the actual thickening, pushed forward by its projection. -/
def actualPresheaf : TopCat.Presheaf CommRingCat.{u} X :=
  (Opens.map (projection f).base).op ⋙ (thickening f).presheaf

/-- The actual second projection applied to a constant dual-number section. -/
def testSectionMap (U : X.Opens) :
    CommRingCat.of (DualNumber k) ⟶ Γ(thickening f, projection f ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv ≫
    (structureMap f).appLE ⊤ _ (by simp)

@[reassoc]
lemma testSectionMap_naturality {U V : X.Opens} (h : V ≤ U) :
    testSectionMap f U ≫ (thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op =
      testSectionMap f V := by
  unfold testSectionMap
  rw [Category.assoc]
  congr 1
  exact (structureMap f).appLE_map (by simp)
    (((Opens.map (projection f).base).map (homOfLE h)).op)

/-- The actual epsilon section, over the inverse image of an open. -/
def epsilonSection (U : X.Opens) : Γ(thickening f, projection f ⁻¹ᵁ U) :=
  testSectionMap f U (DualNumber.eps : DualNumber k)

lemma epsilonSection_mul_self (U : X.Opens) :
    epsilonSection f U * epsilonSection f U = 0 := by
  rw [epsilonSection, ← map_mul, DualNumber.eps_mul_eps, map_zero]

/-- The canonical map sends `a + epsilon b` to the two pullbacks times epsilon. -/
def sectionMap (U : X.Opens) :
    DualNumber Γ(X, U) →+* Γ(thickening f, projection f ⁻¹ᵁ U) := by
  letI := (projection f).app U |>.hom.toAlgebra
  exact (DualNumber.lift ⟨(Algebra.ofId Γ(X, U) _,
    epsilonSection f U), epsilonSection_mul_self f U, fun _ ↦ Commute.all _ _⟩).toRingHom

lemma sectionMap_apply (U : X.Opens) (z : DualNumber Γ(X, U)) :
    sectionMap f U z =
      (projection f).app U z.fst + (projection f).app U z.snd * epsilonSection f U :=
  rfl

@[simp]
lemma sectionMap_inl (U : X.Opens) (a : Γ(X, U)) :
    sectionMap f U (TrivSqZeroExt.inl a) = (projection f).app U a := by
  simp [sectionMap_apply]

@[simp]
lemma sectionMap_eps (U : X.Opens) :
    sectionMap f U (DualNumber.eps : DualNumber Γ(X, U)) = epsilonSection f U := by
  simp [sectionMap_apply]

lemma sectionMap_naturality {U V : X.Opens} (h : V ≤ U) :
    (sectionMap f V).comp (coefficientMap (X.presheaf.map (homOfLE h).op).hom) =
      ((thickening f).presheaf.map
        ((Opens.map (projection f).base).map (homOfLE h)).op).hom.comp
          (sectionMap f U) := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply, sectionMap_apply, coefficientMap_fst,
    coefficientMap_snd, map_add, map_mul]
  have hp := (projection f).naturality (homOfLE h).op
  have ha := congrArg (fun r ↦ r.hom z.fst) hp
  have hb := congrArg (fun r ↦ r.hom z.snd) hp
  have he := congrArg (fun r ↦ r.hom (DualNumber.eps : DualNumber k))
    (testSectionMap_naturality f h)
  change _ = _ at ha hb
  change (thickening f).presheaf.map
    ((Opens.map (projection f).base).map (homOfLE h)).op
      (epsilonSection f U) = epsilonSection f V at he
  rw [← he]
  exact congrArg₂ (· + ·) ha (congrArg₂ (· * ·) hb rfl)

/-- The canonical section maps commute with restriction to smaller opens. -/
def structureComparison : splitPresheaf (X := X) ⟶ actualPresheaf f where
  app U := CommRingCat.ofHom (sectionMap f U.unop)
  naturality {U V} h := by
    apply CommRingCat.hom_ext
    exact sectionMap_naturality f h.unop.le

/-- Dual-number sections glue coordinatewise. -/
lemma splitPresheaf_isSheaf : (splitPresheaf (X := X)).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget CommRingCat)]
  apply TopCat.Presheaf.isSheaf_of_isSheafUniqueGluing_types
  intro ι U s hs
  have hf := X.sheaf.existsUnique_gluing U (fun i ↦ (s i).fst)
    (fun i j ↦ congrArg TrivSqZeroExt.fst (hs i j))
  have hd := X.sheaf.existsUnique_gluing U (fun i ↦ (s i).snd)
    (fun i j ↦ congrArg TrivSqZeroExt.snd (hs i j))
  obtain ⟨a, ha, hua⟩ := hf
  obtain ⟨b, hb, hub⟩ := hd
  refine ⟨⟨a, b⟩, fun i ↦ TrivSqZeroExt.ext (ha i) (hb i), ?_⟩
  intro z hz
  exact TrivSqZeroExt.ext
    (hua z.fst fun i ↦ congrArg TrivSqZeroExt.fst (hz i))
    (hub z.snd fun i ↦ congrArg TrivSqZeroExt.snd (hz i))

set_option backward.isDefEq.respectTransparency false in
instance projection_isAffineHom : IsAffineHom (projection f) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom)
    f (dualNumberProjection k) inferInstance

/-- Restricting the actual pullback to an open gives the expected pullback. -/
lemma open_isPullback (U : X.Opens) :
    IsPullback (projection f ∣_ U)
      ((projection f ⁻¹ᵁ U).ι ≫ structureMap f)
      (U.ι ≫ f) (dualNumberProjection k) :=
  (isPullback_morphismRestrict (projection f) U).paste_vert
    (IsPullback.of_hasPullback f (dualNumberProjection k))

/-- The base-field sections on an open, with the canonical spectrum normalization. -/
def baseSectionMap (U : X.Opens) : CommRingCat.of k ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp)

set_option backward.isDefEq.respectTransparency false in
lemma open_appTop {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (g : Y ⟶ Spec R) (U : Y.Opens) :
    (U.ι ≫ g).appTop ≫ U.topIso.hom = g.appLE ⊤ U (by simp) := by
  rw [Scheme.Hom.comp_appTop]
  change g.app ⊤ ≫ Y.presheaf.map _ ≫ Y.presheaf.map _ = _
  rw [← Functor.map_comp]
  rfl

/-- On an affine open, the actual rings of sections form the expected pushout. -/
lemma affine_isPushout (U : X.Opens) (hU : IsAffineOpen U) :
    IsPushout (baseSectionMap f U)
      (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      ((projection f).app U) (testSectionMap f U) := by
  let : IsAffine U.toScheme := hU
  refine (isPushout_appTop_of_isPullback (open_isPullback f U)).of_iso
    (Scheme.ΓSpecIso (CommRingCat.of k)) U.topIso
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k)))
    (projection f ⁻¹ᵁ U).topIso ?_ ?_ ?_ ?_
  · simpa only [baseSectionMap, Iso.hom_inv_id_assoc] using open_appTop f U
  · exact Scheme.ΓSpecIso_naturality _
  · rw [← Scheme.Hom.resLE_eq_morphismRestrict (projection f) (U := U)]
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE, homOfLE_refl, op_id]
    simp
  · simpa only [testSectionMap, Iso.hom_inv_id_assoc] using
      open_appTop (structureMap f) (projection f ⁻¹ᵁ U)

/-- The coefficientwise dual numbers satisfy the same pushout property. -/
lemma split_isPushout (R : Type u) [CommRing R] [Algebra k R] :
    IsPushout (CommRingCat.ofHom (algebraMap k R))
      (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      (CommRingCat.ofHom (TrivSqZeroExt.inlHom R R))
      (CommRingCat.ofHom (coefficientMap (algebraMap k R))) := by
  refine (CommRingCat.isPushout_tensorProduct k R (DualNumber k)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (DualNumberBaseChange.tensorEquiv k R).toRingEquiv.toCommRingCatIso
    (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact DualNumberBaseChange.tensorTo_includeLeft k R a
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact DualNumberBaseChange.tensorTo_includeRight k R z

lemma affine_sectionMap_isIso (U : X.Opens) (hU : IsAffineOpen U) :
    IsIso (CommRingCat.ofHom (sectionMap f U)) := by
  let := (baseSectionMap f U).hom.toAlgebra
  let hs := split_isPushout (k := k) Γ(X, U)
  let ha := affine_isPushout f U hU
  let e := hs.isoIsPushout _ _ ha
  have he : CommRingCat.ofHom (sectionMap f U) = e.hom := by
    apply CommRingCat.hom_ext
    apply DualNumber.ringHom_ext
    · apply RingHom.ext
      intro a
      have h := congrArg (fun r ↦ r.hom a) (hs.inl_isoIsPushout_hom _ _ ha)
      change sectionMap f U (TrivSqZeroExt.inl a) = e.hom (TrivSqZeroExt.inl a)
      rw [sectionMap_inl]
      exact h.symm
    · have h := congrArg (fun r ↦ r.hom (DualNumber.eps : DualNumber k))
        (hs.inr_isoIsPushout_hom _ _ ha)
      change e.hom (coefficientMap (baseSectionMap f U).hom DualNumber.eps) =
        epsilonSection f U at h
      change sectionMap f U DualNumber.eps = e.hom DualNumber.eps
      simpa only [coefficientMap_eps, sectionMap_eps] using h.symm
  rw [he]
  infer_instance

/-- The split structure sheaf, with coordinatewise gluing. -/
def splitSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  ⟨splitPresheaf, splitPresheaf_isSheaf⟩

/-- The structure sheaf of the actual thickening, pushed forward to the original scheme. -/
def actualSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward _ (projection f).base).obj (thickening f).sheaf

/-- The canonical comparison as a morphism of sheaves of rings. -/
def sheafComparison : splitSheaf (X := X) ⟶ actualSheaf f :=
  ⟨structureComparison f⟩

instance sheafComparison_isIso : IsIso (sheafComparison f) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis
    (B := fun U : X.affineOpens ↦ U.val)
    (by simpa only [Subtype.range_val] using X.isBasis_affineOpens)
  intro U
  exact affine_sectionMap_isIso f U.val U.property

instance structureComparison_isIso : IsIso (structureComparison f) := by
  change IsIso ((TopCat.Sheaf.forget _ X).map (sheafComparison f))
  infer_instance

instance sectionMap_isIso (U : X.Opens) :
    IsIso (CommRingCat.ofHom (sectionMap f U)) := by
  let := structureComparison_isIso f
  change IsIso ((structureComparison f).app (op U))
  exact NatIso.isIso_app_of_isIso (structureComparison f) (op U)

/-- Sections of the actual thickening are canonically the dual numbers of sections. -/
def sectionEquiv (U : X.Opens) :
    DualNumber Γ(X, U) ≃+* Γ(thickening f, projection f ⁻¹ᵁ U) :=
  (asIso (CommRingCat.ofHom (sectionMap f U))).commRingCatIsoToRingEquiv

@[simp]
lemma sectionEquiv_apply (U : X.Opens) (z : DualNumber Γ(X, U)) :
    sectionEquiv f U z = sectionMap f U z := rfl

end Langlands.AlgebraicGeometry.Picard.DualNumberThickening
