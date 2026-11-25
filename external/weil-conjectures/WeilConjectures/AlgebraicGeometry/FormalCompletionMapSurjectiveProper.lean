/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentSheafHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHom
import WeilConjectures.AlgebraicGeometry.FormalFunctionsCompleteBase
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry
private noncomputable def sectionsOfTop {X : Scheme.{u}} (M : X.Modules)
    (x : M.val.obj (Opposite.op ⊤)) : M.sections :=
  M.val.sectionsMk
    (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x)
    (by
      intro U V g
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

private theorem sections_top_injective {X : Scheme.{u}} (M : X.Modules) :
    Function.Injective (fun s : M.sections ↦ s.val (Opposite.op ⊤)) := by
  intro s t h
  change s.val (Opposite.op ⊤) = t.val (Opposite.op ⊤) at h
  apply PresheafOfModules.sections_ext
  intro U
  rw [← PresheafOfModules.sections_property s (homOfLE le_top).op,
    ← PresheafOfModules.sections_property t (homOfLE le_top).op, h]

private theorem hom_sections_natural {X : Scheme.{u}}
    {M N M' N' : X.Modules} (a : M' ⟶ M) (b : N ⟶ N')
    (s : (SheafOfModules.homObj (R := X.sheaf) M N).sections) :
    SheafOfModules.homObjSectionsEquiv (R := X.sheaf) M' N'
      (SheafOfModules.sectionsMap (SheafOfModules.homObjMap (R := X.sheaf) a b) s) =
      a ≫ SheafOfModules.homObjSectionsEquiv (R := X.sheaf) M N s ≫ b := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary surjectivity part of formal completion full faithfulness.
Source: Stacks Project, Cohomology of Schemes, Lemma 0883 (lemma-fully-faithful).
Proof: Let H be the internal Hom sheaf. Given a morphism between completed modules,
invert the completion-internal-Hom bijection to obtain its compatible reductions and then
invert formal functions to obtain a global section of H. The corresponding coherent-module
morphism completes to the given morphism.
(blueprint: lem-weil-pbc-formal-completion-map-surjective-proper). -/
theorem formalCompletion_map_surjective_of_proper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (G F : CoherentModules X) :
    Function.Surjective
      (fun v : G ⟶ F ↦
        (@completion X (isNoetherian_of_locallyOfFiniteType f)
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)).map v) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let J := ((Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
  let H : CoherentModules X := ⟨SheafOfModules.homObj (R := X.sheaf) G.obj F.obj,
    Scheme.Modules.isCoherent_homObj X F.obj G.obj F.property G.property⟩
  obtain ⟨_, _, e, he, _, Φ, hΦ, hbij⟩ := completion_internal_hom_bijective J F G
  obtain ⟨E, hE⟩ := globalSections_formalFunctions_complete_base I f H
  intro v
  obtain ⟨s, hs⟩ := hbij.2 v
  let Γ := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let D := formalCompletionSystem J H.obj ⋙ Γ
  let t : (D ⋙ forget (ModuleCat A)).sections :=
    ⟨fun n ↦ (s.val n).val (Opposite.op ⊤), fun {a b} g ↦
      congrArg (fun z ↦ z.val (Opposite.op ⊤)) (s.property a b g)⟩
  let L := Limits.Types.isLimitEquivSections
    (Limits.isLimitOfPreserves (forget (ModuleCat A)) (Limits.limit.isLimit D))
  let x := E.inv (L.symm t)
  let z : H.obj.sections := sectionsOfTop H.obj x
  have hz (n : ℕᵒᵖ) :
      SheafOfModules.sectionsMap (formalModuleQuotientπ J (n.unop + 1) H.obj) z =
        s.val n := by
    apply sections_top_injective
    have hproj := ConcreteCategory.congr_hom (hE n.unop) x
    have hEx : E.hom x = L.symm t := by
      change (E.inv ≫ E.hom) (L.symm t) = L.symm t
      simp
    change (Limits.limit.π D n) (E.hom x) = (Γ.map _) x at hproj
    rw [hEx] at hproj
    have ht := congrArg (fun w ↦ w.val n) (L.apply_symm_apply t)
    change (formalModuleQuotientπ J (n.unop + 1) H.obj).val.app (Opposite.op ⊤) x =
      (s.val n).val (Opposite.op ⊤)
    exact hproj.symm.trans ht
  let u : G ⟶ F := ⟨SheafOfModules.homObjSectionsEquiv (R := X.sheaf) G.obj F.obj z⟩
  refine ⟨u, ?_⟩
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  rw [← hs, hΦ]
  have : Epi (formalModuleQuotientπ J (n.unop + 1) G.obj) :=
    inferInstanceAs (Epi (Limits.cokernel.π
      (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n.unop + 1)).2
        G.obj)))
  apply (cancel_epi (formalModuleQuotientπ J (n.unop + 1) G.obj)).1
  have hn := congrArg (fun k ↦ SheafOfModules.sectionsMap k z) (he n)
  rw [SheafOfModules.sectionsMap_comp, SheafOfModules.sectionsMap_comp,
    hz] at hn
  have hn' := congrArg
    (SheafOfModules.homObjSectionsEquiv (R := X.sheaf) G.obj
      (formalModuleQuotient J (n.unop + 1) F.obj)) hn
  rw [hom_sections_natural, hom_sections_natural] at hn'
  change formalModuleQuotientπ J (n.unop + 1) G.obj ≫
      formalModuleQuotientMap J u.hom (Nat.le_refl (n.unop + 1)) = _
  simpa only [formalModuleQuotientMap, formalModuleQuotientπ, Limits.cokernel.π_desc,
    Category.id_comp, Category.comp_id] using hn'.symm
end AlgebraicGeometry
