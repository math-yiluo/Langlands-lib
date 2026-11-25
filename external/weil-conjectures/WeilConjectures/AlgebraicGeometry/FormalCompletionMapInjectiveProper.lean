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

private theorem homSections_map {X : Scheme.{u}} {M N M' N' : X.Modules}
    (a : M' ⟶ M) (b : N ⟶ N')
    (s : (SheafOfModules.homObj (R := X.sheaf) M N).sections) :
    SheafOfModules.homObjSectionsEquiv (R := X.sheaf) M' N'
      (SheafOfModules.sectionsMap (SheafOfModules.homObjMap (R := X.sheaf) a b) s) =
    a ≫ SheafOfModules.homObjSectionsEquiv (R := X.sheaf) M N s ≫ b := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary injectivity part of formal completion full faithfulness.
Source: Stacks Project, Cohomology of Schemes, Lemma 0883 (lemma-fully-faithful).
Proof: Let H be the internal Hom sheaf. Formal functions gives a bijection from global
sections of H to the inverse limit of the global sections of H modulo powers of the ideal
sheaf. The completion-internal-Hom comparison gives a bijection from that inverse limit to
morphisms between completed modules. Their composite is the completion map, so equality
after completion implies equality before completion.
(blueprint: lem-weil-pbc-formal-completion-map-injective-proper). -/
theorem formalCompletion_map_injective_of_proper
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (G F : CoherentModules X) :
    Function.Injective
      (fun v : G ⟶ F ↦
        (@completion X (isNoetherian_of_locallyOfFiniteType f)
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)).map v) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let H : CoherentModules X := ⟨SheafOfModules.homObj (R := X.sheaf) G.obj F.obj,
    Scheme.Modules.isCoherent_homObj X F.obj G.obj F.property G.property⟩
  obtain ⟨_, _, e, he, _, Φ, hΦ, hbij⟩ := completion_internal_hom_bijective J F G
  let E := SheafOfModules.homObjSectionsEquiv (R := X.sheaf) G.obj F.obj
  -- A section determines its compatible family of reductions.
  let red (s : H.obj.sections) :
      {t : ∀ n : ℕᵒᵖ, (formalModuleQuotient J (n.unop + 1) H.obj).sections //
        ∀ (a b : ℕᵒᵖ) (g : a ⟶ b),
          SheafOfModules.sectionsMap ((formalCompletionSystem J H.obj).map g) (t a) =
            t b} :=
    ⟨fun n ↦ SheafOfModules.sectionsMap (formalModuleQuotientπ J (n.unop + 1) H.obj) s,
      by
        intro a b g
        rw [← SheafOfModules.sectionsMap_comp]
        change SheafOfModules.sectionsMap
          (formalModuleQuotientπ J (a.unop + 1) H.obj ≫
            formalModuleQuotientMap J (𝟙 H.obj)
              (Nat.succ_le_succ (leOfHom g.unop))) s = _
        simp [formalModuleQuotientπ, formalModuleQuotientMap]⟩
  -- The comparison agrees with completion after every quotient projection.
  have hcomp (v : G ⟶ F) : Φ (red (E.symm v.hom)) = (completion X J).map v := by
    apply ObjectProperty.hom_ext _
    apply NatTrans.ext
    funext n
    rw [hΦ]
    have : Epi (formalModuleQuotientπ J (n.unop + 1) G.obj) :=
      inferInstanceAs (Epi (Limits.cokernel.π _))
    apply (cancel_epi (formalModuleQuotientπ J (n.unop + 1) G.obj)).1
    have hn := congrArg
      (fun k ↦ SheafOfModules.homObjSectionsEquiv (R := X.sheaf) G.obj
        (formalModuleQuotient J (n.unop + 1) F.obj)
        (SheafOfModules.sectionsMap k (E.symm v.hom))) (he n)
    rw [SheafOfModules.sectionsMap_comp, SheafOfModules.sectionsMap_comp,
      homSections_map, homSections_map] at hn
    simp only [Category.id_comp, Category.comp_id] at hn
    change _ = v.hom ≫ formalModuleQuotientπ J (n.unop + 1) F.obj at hn
    change _ = formalModuleQuotientπ J (n.unop + 1) G.obj ≫
      formalModuleQuotientMap J v.hom (Nat.le_refl (n.unop + 1))
    simpa [red, E, formalModuleQuotientMap, formalModuleQuotientπ] using hn
  intro v w hvw
  have hr : red (E.symm v.hom) = red (E.symm w.hom) := by
    apply hbij.1
    rw [hcomp, hcomp]
    exact hvw
  -- Formal functions recovers the global section from these reductions.
  obtain ⟨q, hq⟩ := globalSections_formalFunctions_complete_base I f H
  let T := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  have htop : (E.symm v.hom).val (Opposite.op ⊤) = (E.symm w.hom).val (Opposite.op ⊤) := by
    apply (ModuleCat.mono_iff_injective q.hom).mp inferInstance
    apply Limits.Concrete.limit_ext (formalCompletionSystem J H.obj ⋙ T)
    intro n
    have hn := ConcreteCategory.congr_hom (hq n.unop) ((E.symm v.hom).val (Opposite.op ⊤))
    have hm := ConcreteCategory.congr_hom (hq n.unop) ((E.symm w.hom).val (Opposite.op ⊤))
    rw [ModuleCat.comp_apply] at hn hm
    rw [hn, hm]
    exact congrArg (fun t ↦ (t.val n).val (Opposite.op ⊤)) hr
  apply ObjectProperty.hom_ext _
  apply E.symm.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hv := (E.symm v.hom).property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hw := (E.symm w.hom).property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  rw [← hv, ← hw, htop]
end AlgebraicGeometry
