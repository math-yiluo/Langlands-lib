import Langlands.GroupScheme.RelativeUnipotent.AffineSectionCoordinates
import Langlands.AlgebraicGeometry.Modules.FlatSectionDescent
import Langlands.AlgebraicGeometry.Modules.LineBundleFlatDescentStr

/-! # Descent for the canonical relative-section pullback -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.SchemeModule Langlands.Scheme.Modules
open Langlands.SchemeModule.RigidifiedModule
open Langlands.Scheme.Modules.LineBundleFlatDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent

variable {S : Scheme.{u}} (M : S.Modules)

lemma compIso_hom_pullbackSection {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c)
    (N : Z.Modules) (s : GlobalSections N) :
    (compIso a b c h N).hom.app ⊤
        (pullbackSection a ((Scheme.Modules.pullback b).obj N)
          (pullbackSection b N s)) = pullbackSection c N s := by
  rw [compIso_hom]
  have htop {A B : Scheme.{u}} (f : A ⟶ B) (Q : B.Modules) (t : GlobalSections Q) :
      pullbackSection f Q t = sectionPullbackLE f Q (show ⊤ ≤ f ⁻¹ᵁ ⊤ by simp) t := by
    rw [pullbackSection_eq_sectionPullback]
    exact (sectionPullbackLE_self f Q ⊤ t).symm
  simp only [compHom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, htop]
  erw [pullbackComp_hom_sectionPullbackLE a b N
    (show ⊤ ≤ b ⁻¹ᵁ ⊤ by simp) (show ⊤ ≤ a ⁻¹ᵁ ⊤ by simp)
    (show ⊤ ≤ (a ≫ b) ⁻¹ᵁ ⊤ by simp) s]
  exact pullbackCongr_hom_sectionPullbackLE h N (by simp) (by simp) s

lemma sectionPullback_comp {T U W : Over S} (a : W ⟶ U) (b : U ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback T.hom).obj M)) :
    sectionPullback M a (sectionPullback M b s) =
      sectionPullback M (a ≫ b) s := by
  have H := compIso_assoc a.left b.left T.hom (a ≫ b).left U.hom W.hom
    rfl (Over.w b) (Over.w a) (Over.w (a ≫ b)) M
  change (compIso a.left U.hom W.hom (Over.w a) M).hom.app ⊤
      (pullbackSection a.left ((Scheme.Modules.pullback U.hom).obj M)
        ((compIso b.left T.hom U.hom (Over.w b) M).hom.app ⊤
          (pullbackSection b.left ((Scheme.Modules.pullback T.hom).obj M) s))) = _
  rw [pullbackSection_naturality]
  change ((Scheme.Modules.pullback a.left).map
      (compIso b.left T.hom U.hom (Over.w b) M).hom ≫
      (compIso a.left U.hom W.hom (Over.w a) M).hom).app ⊤
      (pullbackSection a.left _ (pullbackSection b.left _ s)) = _
  rw [← H, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    compIso_hom_pullbackSection]
  rfl

/-- A flat surjective test map detects equality under the exact section pullback. -/
lemma sectionPullback_injective {T U : Over S} (b : U ⟶ T)
    [Flat b.left] [Surjective b.left] :
    Function.Injective (sectionPullback M b) := by
  intro s t h
  apply Langlands.AlgebraicGeometry.Modules.pullbackSection_injective b.left _
  apply (ConcreteCategory.bijective_of_isIso
    ((compIso b.left T.hom U.hom (Over.w b) M).hom.app ⊤)).injective
  exact h

/-- Normalize a cover section back to the iterated pullback sheaf. -/
def iteratedSection {T U : Over S} (b : U ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M)) :
    GlobalSections ((Scheme.Modules.pullback b.left).obj
      ((Scheme.Modules.pullback T.hom).obj M)) :=
  (compIso b.left T.hom U.hom (Over.w b) M).inv.app ⊤ s

/-- A further section pullback of the normalized section, transported to a common
composite, is the prescribed relative pullback of the original section. -/
lemma iteratedSection_pullback {T U W : Over S} (b : U ⟶ T) (a : W ⟶ U)
    (d : W ⟶ T) (hd : a ≫ b = d)
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M)) :
    ((compIso a.left b.left d.left (congrArg (fun f => f.left) hd)
        ((Scheme.Modules.pullback T.hom).obj M)).hom ≫
      (compIso d.left T.hom W.hom (Over.w d) M).hom).app ⊤
      (pullbackSection a.left _ (iteratedSection M b s)) =
      sectionPullback M a s := by
  rw [compIso_assoc a.left b.left T.hom d.left U.hom W.hom
    (congrArg (fun f => f.left) hd) (Over.w b) (Over.w a) (Over.w d) M]
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ← pullbackSection_naturality]
  simp only [iteratedSection, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

/-- The matching equation for relative sections on all tests over the base. -/
def SectionCompatible {T U : Over S} (b : U ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M)) : Prop :=
  ∀ (W : Over S) (a c : W ⟶ U), a ≫ b = c ≫ b →
    sectionPullback M a s = sectionPullback M c s

lemma iteratedSection_compatible_over {T U W : Over S} (b : U ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M))
    (hs : SectionCompatible M b s) (a c : W ⟶ U) (h : a ≫ b = c ≫ b) :
    (equalCompositeIso b.left a.left c.left (congrArg (fun f => f.left) h)
        ((Scheme.Modules.pullback T.hom).obj M)).hom.app ⊤
        (pullbackSection a.left _ (iteratedSection M b s)) =
      pullbackSection c.left _ (iteratedSection M b s) := by
  let N := (Scheme.Modules.pullback T.hom).obj M
  let A := compIso a.left b.left (a ≫ b).left rfl N
  let C := compIso c.left b.left (a ≫ b).left
    (congrArg (fun f => f.left) h.symm) N
  let J := compIso (a ≫ b).left T.hom W.hom (Over.w (a ≫ b)) M
  have Ha := iteratedSection_pullback M b a (a ≫ b) rfl s
  have Hc := iteratedSection_pullback M b c (a ≫ b) h.symm s
  have H : (A.hom ≫ J.hom).app ⊤
        (pullbackSection a.left _ (iteratedSection M b s)) =
      (C.hom ≫ J.hom).app ⊤
        (pullbackSection c.left _ (iteratedSection M b s)) :=
    Ha.trans ((hs W a c h).trans Hc.symm)
  apply (ConcreteCategory.bijective_of_isIso ((C.hom ≫ J.hom).app ⊤)).injective
  rw [equalCompositeIso_hom_eq_compIso b.left a.left c.left
    (congrArg (fun f => f.left) h) (a ≫ b).left rfl
    (congrArg (fun f => f.left) h.symm)]
  change (C.hom ≫ J.hom).app ⊤ ((A.hom ≫ C.inv).app ⊤ _) = _
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using H

/-- The relative matching condition gives the genuine raw module overlap equations. -/
lemma iteratedSection_compatible {T U : Over S} (b : U ⟶ T)
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M))
    (hs : SectionCompatible M b s) :
    Langlands.AlgebraicGeometry.Modules.PullbackSectionCompatible b.left
      ((Scheme.Modules.pullback T.hom).obj M) (iteratedSection M b s) := by
  intro W a c h
  let V : Over S := Over.mk (a ≫ U.hom)
  let aa : V ⟶ U := Over.homMk a rfl
  have hc : c ≫ U.hom = a ≫ U.hom := by
    rw [← Over.w b, ← Category.assoc, ← Category.assoc, h]
  let cc : V ⟶ U := Over.homMk c hc
  have he : aa ≫ b = cc ≫ b := by
    ext
    exact h
  exact iteratedSection_compatible_over M b s hs aa cc he

/-- A compatible relative section descends uniquely along an affine flat surjection. -/
lemma existsUnique_section_of_compatible {T U : Over S} (b : U ⟶ T)
    [IsAffineHom b.left] [Flat b.left] [Surjective b.left]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M))
    (hs : SectionCompatible M b s) :
    ∃! t : GlobalSections ((Scheme.Modules.pullback T.hom).obj M),
      sectionPullback M b t = s := by
  obtain ⟨t, ht, -⟩ :=
    Langlands.AlgebraicGeometry.Modules.existsUnique_section_of_compatible b.left
      ((Scheme.Modules.pullback T.hom).obj M) (iteratedSection M b s)
      (iteratedSection_compatible M b s hs)
  have ht' : sectionPullback M b t = s := by
    change (compIso b.left T.hom U.hom (Over.w b) M).hom.app ⊤
      (pullbackSection b.left _ t) = s
    rw [ht]
    simp only [iteratedSection, ← ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.comp_app, Iso.inv_hom_id, Scheme.Modules.Hom.id_app]
    rfl
  exact ⟨t, ht', fun t' ht'' => sectionPullback_injective M b (ht''.trans ht'.symm)⟩

/-- Choose the unique descended relative section using its actual matching equations. -/
def sectionOfCompatible {T U : Over S} (b : U ⟶ T)
    [IsAffineHom b.left] [Flat b.left] [Surjective b.left]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M))
    (hs : SectionCompatible M b s) :
    GlobalSections ((Scheme.Modules.pullback T.hom).obj M) :=
  (existsUnique_section_of_compatible M b s hs).choose

@[simp]
lemma sectionPullback_sectionOfCompatible {T U : Over S} (b : U ⟶ T)
    [IsAffineHom b.left] [Flat b.left] [Surjective b.left]
    [M.IsQuasicoherent]
    (s : GlobalSections ((Scheme.Modules.pullback U.hom).obj M))
    (hs : SectionCompatible M b s) :
    sectionPullback M b (sectionOfCompatible M b s hs) = s :=
  (existsUnique_section_of_compatible M b s hs).choose_spec.1

end Langlands.GroupScheme.RelativeUnipotent
