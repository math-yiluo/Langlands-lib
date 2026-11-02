import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldPoincareTangentSectionsStatement
import Langlands.AlgebraicGeometry.Picard.DualNumberSectionTrivialization
import Langlands.AlgebraicGeometry.Picard.DualPointOriginTriviality
import Langlands.AlgebraicGeometry.Modules.SectionVanishingTransportProof
import Langlands.AlgebraicGeometry.LinearSystem.SectionRatio
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Sections of the Poincaré bundle along a nonzero tangent vector at the origin -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.SchemeModule Langlands.Scheme.Modules

section OriginFibre

variable {S : Scheme.{u}} (A : AbelianScheme S) (hA : HasDualScheme A)

/-- The section `a ↦ (a, 0)` of the Poincaré projection over the origin of the dual. -/
def originFibreSection : A.X.left ⟶ pullback A.X.hom (dualScheme A hA).hom :=
  pullback.lift (𝟙 A.X.left) (A.X.hom ≫ (dualOrigin A hA).left) (by
    rw [Category.assoc, Over.w (dualOrigin A hA)]
    simp)

@[reassoc (attr := simp)]
lemma originFibreSection_fst :
    originFibreSection A hA ≫ pullback.fst A.X.hom (dualScheme A hA).hom = 𝟙 A.X.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma originFibreSection_snd :
    originFibreSection A hA ≫ pullback.snd A.X.hom (dualScheme A hA).hom =
      A.X.hom ≫ (dualOrigin A hA).left :=
  pullback.lift_snd _ _ _

/-- The origin classifies the trivial rigidified family, so its Poincaré pullback is
trivial as a line bundle on the relative space over the base. -/
lemma nonempty_dualPointFamily_origin_iso :
    Nonempty ((RigidifiedLineBundle.forget _).obj (dualPointFamily A hA (dualOrigin A hA)) ≅
      LineBundle.trivial ((relativeSpace A.X.hom).obj (Over.mk (𝟙 S)))) := by
  have hid : (Over.homMk (Over.mk (𝟙 S)).hom : Over.mk (𝟙 S) ⟶ Over.mk (𝟙 S)) =
      𝟙 (Over.mk (𝟙 S)) := by
    apply Over.OverMorphism.ext
    rfl
  have h := dualPointClass_origin picardZeroPullback A hA (Over.mk (𝟙 S))
  rw [hid, Category.id_comp] at h
  have hv := congrArg Subtype.val h
  obtain ⟨r⟩ := Quotient.exact hv
  exact ⟨(RigidifiedLineBundle.forget _).mapIso r⟩

/-- The Poincaré bundle is trivial on the fibre over the origin of the dual. -/
lemma nonempty_originFibreSection_pullback_iso :
    Nonempty ((Scheme.Modules.pullback (originFibreSection A hA)).obj
        (poincareLineBundle A hA).obj ≅ structureModule A.X.left) := by
  obtain ⟨r⟩ := nonempty_dualPointFamily_origin_iso A hA
  let D := dualScheme A hA
  let r₀ : A.X.left ⟶ (relativeSpace A.X.hom).obj (Over.mk (𝟙 S)) :=
    pullback.lift A.X.hom (𝟙 A.X.left) (by simp)
  let m := (relativeSpace A.X.hom).map (dualOrigin A hA)
  let L₀ := (RigidifiedLineBundle.forget _).obj (poincareFamily A hA)
  have hm₁ : m ≫ pullback.fst D.hom A.X.hom =
      pullback.fst (𝟙 S) A.X.hom ≫ (dualOrigin A hA).left :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd D.hom A.X.hom = pullback.snd (𝟙 S) A.X.hom :=
    pullback.lift_snd _ _ _
  have hr₁ : r₀ ≫ pullback.fst (𝟙 S) A.X.hom = A.X.hom := pullback.lift_fst _ _ _
  have hr₂ : r₀ ≫ pullback.snd (𝟙 S) A.X.hom = 𝟙 A.X.left := pullback.lift_snd _ _ _
  have hc : originFibreSection A hA ≫ (relativeSpaceSymmetry A.X.hom D).inv = r₀ ≫ m := by
    apply pullback.hom_ext
    · calc (originFibreSection A hA ≫ (relativeSpaceSymmetry A.X.hom D).inv) ≫
            pullback.fst D.hom A.X.hom
          = originFibreSection A hA ≫ ((relativeSpaceSymmetry A.X.hom D).inv ≫
            pullback.fst D.hom A.X.hom) := Category.assoc _ _ _
        _ = originFibreSection A hA ≫ pullback.snd A.X.hom D.hom :=
          congrArg (originFibreSection A hA ≫ ·) (pullbackSymmetry_inv_comp_fst D.hom A.X.hom)
        _ = A.X.hom ≫ (dualOrigin A hA).left := originFibreSection_snd A hA
        _ = (r₀ ≫ pullback.fst (𝟙 S) A.X.hom) ≫ (dualOrigin A hA).left := by rw [hr₁]
        _ = r₀ ≫ (m ≫ pullback.fst D.hom A.X.hom) := by rw [hm₁, Category.assoc]
        _ = (r₀ ≫ m) ≫ pullback.fst D.hom A.X.hom := (Category.assoc _ _ _).symm
    · calc (originFibreSection A hA ≫ (relativeSpaceSymmetry A.X.hom D).inv) ≫
            pullback.snd D.hom A.X.hom
          = originFibreSection A hA ≫ ((relativeSpaceSymmetry A.X.hom D).inv ≫
            pullback.snd D.hom A.X.hom) := Category.assoc _ _ _
        _ = originFibreSection A hA ≫ pullback.fst A.X.hom D.hom :=
          congrArg (originFibreSection A hA ≫ ·) (pullbackSymmetry_inv_comp_snd D.hom A.X.hom)
        _ = 𝟙 A.X.left := originFibreSection_fst A hA
        _ = r₀ ≫ (m ≫ pullback.snd D.hom A.X.hom) := by rw [hm₂, hr₂]
        _ = (r₀ ≫ m) ≫ pullback.snd D.hom A.X.hom := (Category.assoc _ _ _).symm
  refine ⟨((Scheme.Modules.pullbackComp (originFibreSection A hA)
      (relativeSpaceSymmetry A.X.hom D).inv).app L₀.obj) ≪≫
    (Scheme.Modules.pullbackCongr hc).app L₀.obj ≪≫
    ((Scheme.Modules.pullbackComp r₀ m).app L₀.obj).symm ≪≫
    (Scheme.Modules.pullback r₀).mapIso ((LineBundle.forget _).mapIso r) ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso r₀⟩

end OriginFibre

/-- Over a field, the global functions of an abelian scheme are zero or units. -/
lemma eq_zero_or_isUnit_of_abelianScheme {K : Type u} [Field K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (c : Γ(A.X.left, ⊤)) :
    c = 0 ∨ IsUnit c := by
  have hiso : IsIso (A.X.hom.app ⊤) :=
    Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions A.X.left _ A.X.hom
      inferInstance inferInstance inferInstance ⊤
  obtain ⟨b, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp hiso).2 c
  obtain ⟨a, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)).2 b
  rcases eq_or_ne a 0 with ha | ha
  · left
    rw [ha, map_zero, map_zero]
  · right
    exact ((Ne.isUnit ha).map _).map _

/-- The Poincaré bundle has non-free sections along a nonzero tangent vector at the origin. -/
theorem algClosedFieldPoincareTangentSections :
    AlgClosedFieldPoincareTangentSectionsStatement.{u} := by
  intro K _ _ A hA t ht X q f h
  refine ⟨fun φ ↦ ?_⟩
  let D := dualScheme A hA
  let P := poincareLineBundle A hA
  let M := (Scheme.Modules.pullback q).obj P.obj
  have ht₁ : t ≫ D.hom = dualNumberProjection K := ht.1.1
  have ht₂ : dualNumberAugmentation K ≫ t = (dualOrigin A hA).left := ht.1.2
  -- The global section corresponding to `1`, which is not killed by `ε`.
  let s : Γ(M, ⊤) := φ.inv.hom (1 : DualNumber K)
  have hs : structureRingHom f (DualNumber.eps : DualNumber K) • s ≠ 0 := by
    intro h0
    have h1 : φ.inv.hom ((DualNumber.eps : DualNumber K) • (1 : DualNumber K)) = 0 := by
      rw [map_smul]
      exact h0
    have h2 := congrArg φ.hom.hom h1
    rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply, map_zero,
      smul_eq_mul, mul_one] at h2
    simpa using congrArg TrivSqZeroExt.snd h2
  -- The fibre product is the actual first-order thickening of `A`.
  have h' : IsPullback (q ≫ pullback.fst A.X.hom D.hom) f A.X.hom (dualNumberProjection K) := by
    have := h.paste_horiz (IsPullback.of_hasPullback A.X.hom D.hom)
    rwa [ht₁] at this
  let ψ := h'.isoPullback
  let j : DualNumberThickening.thickening A.X.hom ⟶ X := ψ.inv
  have hjf : j ≫ f = DualNumberThickening.structureMap A.X.hom := h'.isoPullback_inv_snd
  have hjq : j ≫ q ≫ pullback.fst A.X.hom D.hom = DualNumberThickening.projection A.X.hom :=
    h'.isoPullback_inv_fst
  let L : LineBundle (DualNumberThickening.thickening A.X.hom) :=
    (LineBundle.pullback j).obj ((LineBundle.pullback q).obj P)
  -- Its restriction to the closed fibre is trivial.
  have hc₀ : (DualNumberThickening.closedPoint A.X.hom ≫ j) ≫ q = originFibreSection A hA := by
    apply pullback.hom_ext
    · rw [originFibreSection_fst, Category.assoc, Category.assoc, hjq,
        DualNumberThickening.closedPoint_projection]
    · rw [originFibreSection_snd, Category.assoc, Category.assoc]
      erw [h.w]
      rw [← Category.assoc j, hjf, ← Category.assoc,
        DualNumberThickening.closedPoint_structure, Category.assoc, ht₂]
  obtain ⟨e₀⟩ := nonempty_originFibreSection_pullback_iso A hA
  let e : (Scheme.Modules.pullback (DualNumberThickening.closedPoint A.X.hom)).obj L.obj ≅
      structureModule A.X.left :=
    (Scheme.Modules.pullbackComp _ j).app M ≪≫
      (Scheme.Modules.pullbackComp _ q).app P.obj ≪≫
      (Scheme.Modules.pullbackCongr hc₀).app P.obj ≪≫ e₀
  -- The transported section is not killed by `ε`, so it trivializes the deformation.
  let s' : Γ(L.obj, ⊤) := pullbackSection j M s
  have hε : DualNumberThickening.globalEpsilon A.X.hom =
      j.appTop (structureRingHom f (DualNumber.eps : DualNumber K)) := by
    rw [DualNumberThickening.globalEpsilon, ← hjf, Scheme.Hom.comp_appTop]
    rfl
  have hs' : DualNumberThickening.globalEpsilon A.X.hom • s' ≠ 0 := by
    rw [hε]
    change j.appTop _ • pullbackSection j M s ≠ 0
    rw [← Langlands.AlgebraicGeometry.LinearSystem.pullbackSection_smul,
      Ne, pullbackSection_iso_eq_zero_iff]
    exact hs
  have hiso := DualNumberThickening.isIso_sectionHom_of_globalEpsilon_smul_ne_zero
    (eq_zero_or_isUnit_of_abelianScheme A) L e s' hs'
  have hpb : IsPullback (j ≫ q) (DualNumberThickening.structureMap A.X.hom)
      ((baseChange (dualScheme A hA).hom).obj A).X.hom t :=
    h.of_iso ψ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [j]) (by simp [← hjf, j])
      (by simp) (by simp)
  let eL : (Scheme.Modules.pullback (j ≫ q)).obj P.obj ≅
      SheafOfModules.unit (DualNumberThickening.thickening A.X.hom).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp j q).app P.obj).symm ≪≫ (asIso (sectionHom L.obj s')).symm
  have horigin := dualPoint_eq_origin_of_isPullback A hA
    (T := Over.mk (t ≫ D.hom)) (Over.homMk t rfl) (j ≫ q)
    (DualNumberThickening.structureMap A.X.hom) hpb eL
  have ht₀ : t = dualNumberProjection K ≫ (dualOrigin A hA).left := by
    have := congrArg (fun g ↦ g.left) horigin
    simp only [Over.comp_left, Over.homMk_left, Over.mk_hom] at this
    rw [ht₁] at this
    exact this
  exact ht.2 ht₀

end Langlands.AbelianScheme
