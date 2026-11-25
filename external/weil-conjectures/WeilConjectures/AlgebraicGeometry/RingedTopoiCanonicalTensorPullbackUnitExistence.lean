/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

@[expose] public section
universe u v u' v'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u}
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))
open scoped ChangeOfRings

private theorem pure_right_unitor
    {E : Type u} [Category.{u} E] {J : GrothendieckTopology E}
    (A : Sheaf J CommRingCat.{u}) (M : SheafOfModules.{u} (RingedTensor.ringSheaf A))
    (W : Eᵒᵖ) (m : M.val.obj W) (r : A.obj.obj W) :
    ((monoidalCategory A).rightUnitor M).hom.val.app W
      (RingedTensor.pure A M (unit (RingedTensor.ringSheaf A)) W m r) = r • m := by
  let := monoidalCategory A
  let F := PresheafOfModules.sheafification (𝟙 (RingedTensor.ringSheaf A).obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (RingedTensor.ringSheaf A).obj)
  let ε (N : SheafOfModules.{u} (RingedTensor.ringSheaf A)) : F.obj N.val ⟶ N :=
    adj.counit.app N
  have he : (tensorObjIsoSheafification M (unit (RingedTensor.ringSheaf A))).inv ≫
      (ρ_ M).hom = F.map (ρ_ M.val).hom ≫ adj.counit.app M := by
    simp only [tensorObjIsoSheafification, Iso.trans_inv, tensorIso_hom,
      Iso.symm_inv, Iso.app_hom, asIso_hom, Functor.Monoidal.μIso_inv, Category.assoc]
    change Functor.OplaxMonoidal.δ F M.val (unit (RingedTensor.ringSheaf A)).val ≫
      (ε M ⊗ₘ ε (unit (RingedTensor.ringSheaf A))) ≫
        (ρ_ M).hom = F.map (ρ_ M.val).hom ≫ ε M
    simp only [tensorHom_def', Category.assoc]
    erw [rightUnitor_naturality]
    rw [Functor.Monoidal.map_rightUnitor]
    simp only [Category.assoc]
    rfl
  have h := congrArg (fun f ↦ f.val.app W
    ((adj.unit.app (M.val ⊗ (unit (RingedTensor.ringSheaf A)).val)).app W
      (m ⊗ₜ[A.obj.obj W] r))) he
  change _ = _ at h
  have hn := adj.unit.naturality (ρ_ M.val).hom
  have hh := congrArg (fun f ↦ f.app W (m ⊗ₜ[A.obj.obj W] r)) hn
  have ht := congrArg (fun f ↦ f.app W (r • m)) (adj.right_triangle_components M)
  exact h.trans ((congrArg ((adj.counit.app M).val.app W) hh.symm).trans ht)

-- Check the transported rank-one action and its sectionwise linear equivalences.
private theorem inverseImage_unit_iso :
    ∃ e : unit (RingedTensor.ringSheaf RI) ≅
        I.modules.obj (unit (RingedTensor.ringSheaf R)),
      (RingedTensor.underlying RI).map e.hom =
        I.ringUnderlying.inv ≫ I.moduleUnderlying.inv.app
          (unit (RingedTensor.ringSheaf R)) := by
  let U := unit (RingedTensor.ringSheaf R)
  let Z := (RingedTensor.underlying R).obj U
  let one : Z ⟶ Z := ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
                        naturality := by
                          intro W V f
                          ext x
                          exact (map_one (R.obj.map f).hom).symm }⟩
  let e : (RingedTensor.underlying RI).obj (I.modules.obj U) ≅
      (sheafCompose JD (CategoryTheory.forget CommRingCat.{u})).obj RI :=
    I.moduleUnderlying.app U ≪≫ I.ringUnderlying
  let g (W : Dᵒᵖ) (r : RI.obj.obj W) : (I.modules.obj U).val.obj W :=
    e.inv.hom.app W r
  have hf (W : Dᵒᵖ) (r : RI.obj.obj W) : g W r = r • g W 1 := by
    let t := I.ringUnderlying.inv.hom.app W r
    have ht : I.ringUnderlying.hom.hom.app W t = r :=
      congrArg (fun f ↦ f.hom.app W r) I.ringUnderlying.inv_hom_id
    have ho := I.ringOne Z one (fun _ _ ↦ rfl) W t
    have hi := congrArg (I.ringUnderlying.inv.hom.app W) ho
    have hc (x : (uInv.obj Z).obj.obj W) :
        I.ringUnderlying.inv.hom.app W (I.ringUnderlying.hom.hom.app W x) = x :=
      congrArg (fun f ↦ f.hom.app W x) I.ringUnderlying.hom_inv_id
    simp only [id_eq] at hi
    simp only [hc] at hi
    have hm := I.moduleSMul U Z (𝟙 Z) one (𝟙 Z)
      (fun W x ↦ (mul_one (show R.obj.obj W from x)).symm) W t
    simp only [uInv.map_id] at hm
    exact hm.trans (congrArg₂
      (fun (a : RI.obj.obj W) (b : (I.modules.obj U).val.obj W) ↦ a • b) ht
      (congrArg ((I.moduleUnderlying.inv.app U).hom.app W) hi))
  let eW (W : Dᵒᵖ) : RI.obj.obj W ≃ₗ[RI.obj.obj W] (I.modules.obj U).val.obj W :=
    { toEquiv := (((sheafToPresheaf JD (Type u)).mapIso e).app W).toEquiv.symm
      map_add' := by
        intro r s
        change g W (r + s) = g W r + g W s
        exact (hf W (r + s)).trans
          ((add_smul r s (g W 1)).trans (congrArg₂ (· + ·) (hf W r).symm (hf W s).symm))
      map_smul' := by
        intro r s
        change g W (r * s) = r • g W s
        exact (hf W (r * s)).trans
          ((mul_smul r s (g W 1)).trans (congrArg (r • ·) (hf W s).symm)) }
  let ep : (unit (RingedTensor.ringSheaf RI)).val ≅ (I.modules.obj U).val :=
    PresheafOfModules.isoMk (fun W ↦ (eW W).toModuleIso) (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      exact congrArg (fun k ↦ k r) (e.inv.hom.naturality f))
  refine ⟨(fullyFaithfulForget _).preimageIso ep, ?_⟩
  rfl

private theorem scalarExtension_unit_iso :
    ∃ e : (RingedTensor.tensorFunctor c).obj (unit (RingedTensor.ringSheaf RI)) ≅
        unit (RingedTensor.ringSheaf S),
      ∀ (W : Dᵒᵖ) (r : RI.obj.obj W),
        e.hom.val.app W
          ((RingedTensor.tensorUnit c (unit (RingedTensor.ringSheaf RI))).hom.app W r) =
            c.hom.app W r := by
  let A := RingedTensor.ringSheaf RI
  let B := RingedTensor.ringSheaf S
  let F := PresheafOfModules.sheafification (𝟙 B.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)
  let eW (W : Dᵒᵖ) :
      (changeOfRingsPresheaf.{u, u, u} c (unit A)).obj W ≅ (unit B).val.obj W := by
    let := (c.hom.app W).hom.toAlgebra
    exact (TensorProduct.AlgebraTensorModule.rid (RI.obj.obj W)
      (S.obj.obj W) (S.obj.obj W)).toModuleIso
  let ep : changeOfRingsPresheaf.{u, u, u} c (unit A) ≅ (unit B).val :=
    PresheafOfModules.isoMk eW (by
      intro W V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s r =>
        change S.obj.obj W at s
        change RI.obj.obj W at r
        change (eW V).hom ((changeOfRingsPresheaf c (unit A)).map f
          (s ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r)) =
            S.obj.map f ((eW W).hom (s ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r))
        erw [tensorRestriction_tmul]
        change c.hom.app V (RI.obj.map f r) * S.obj.map f s =
          S.obj.map f (c.hom.app W r * s)
        rw [map_mul]
        exact congrArg (fun a ↦ a * S.obj.map f s)
          (congrArg (fun k ↦ k r) (c.hom.naturality f)))
  let e : (RingedTensor.tensorFunctor c).obj (unit A) ≅ unit B :=
    F.mapIso ep ≪≫ asIso (adj.counit.app (unit B))
  refine ⟨e, ?_⟩
  intro W r
  erw [tensorUnit_apply]
  let v := (1 : S.obj.obj W) ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom] r
  have hn := adj.unit.naturality ep.hom
  have hh := congrArg (fun f ↦ f.app W v) hn
  have ht := congrArg (fun f ↦ f.app W (c.hom.app W r))
    (adj.right_triangle_components (unit B))
  change (adj.counit.app (unit B)).val.app W
    ((F.map ep.hom).val.app W ((adj.unit.app _).app W v)) = _
  refine (congrArg ((adj.counit.app (unit B)).val.app W) hh.symm).trans ?_
  change (adj.counit.app (unit B)).val.app W
    ((adj.unit.app (unit B).val).app W ((eW W).hom v)) = _
  have hv : (eW W).hom v = c.hom.app W r := by
    change c.hom.app W r * 1 = c.hom.app W r
    exact mul_one _
  rw [hv]
  exact ht

private theorem comparison_q_eq
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf R)) :
    k.q M = RingedTensor.tensorUnit c (I.modules.obj M) ≫
      (RingedTensor.underlying S).map (eqToHom (hobj M).symm) := by
  ext W m
  exact (k.q_one M W m).trans
    (congrArg ((eqToHom (hobj M).symm).val.app W)
      (tensorUnit_apply c (I.modules.obj M) W m).symm)

private theorem comparison_q_hom_ext
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj)
    (M : SheafOfModules.{u} (RingedTensor.ringSheaf R))
    (H : SheafOfModules.{u} (RingedTensor.ringSheaf S))
    {f g : L.obj M ⟶ H}
    (h : k.q M ≫ (RingedTensor.underlying S).map f =
      k.q M ≫ (RingedTensor.underlying S).map g) : f = g := by
  apply (cancel_epi (eqToHom (hobj M).symm)).mp
  apply ((RingedTensor.tensorAdjunction c).homEquiv (I.modules.obj M) H).injective
  apply (RingedTensor.underlying RI).map_injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change RingedTensor.tensorUnit c (I.modules.obj M) ≫
      (RingedTensor.underlying S).map (eqToHom (hobj M).symm ≫ f) =
    RingedTensor.tensorUnit c (I.modules.obj M) ≫
      (RingedTensor.underlying S).map (eqToHom (hobj M).symm ≫ g)
  simpa only [comparison_q_eq R S RI uInv I c L hobj k M,
    Functor.map_comp, Category.assoc] using h

-- Transport scalar extension and evaluate the comparison on generalized unit tensors.
/--
The proof constructs the unit map from pure tensors and scalar extension.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(auxiliary; not a blueprint node).
Proof in words: The proof constructs the unit map from pure tensors and scalar extension. -/
theorem canonicalRingedTensorComparison_unit_exists
    (hmap : ∀ {M N : (SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))} (f : M ⟶ N), L.map f =
      eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
        eqToHom (hobj N).symm)
    (k : CanonicalRingedTensorComparison R S RI uInv I c L hobj) :
    ∃ j :L.obj (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) ≅ SheafOfModules.unit ((sheafCompose JD
      (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ,
      ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
        (k.mu M (SheafOfModules.unit ((sheafCompose JC
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R))).hom ≫
          (monoidalCategory S).tensorHom (𝟙 (L.obj M)) j.hom ≫
            ((monoidalCategory S).rightUnitor (L.obj M)).hom =
          L.map (((monoidalCategory R).rightUnitor M).hom)  := by
  classical
  let := monoidalCategory R
  let := monoidalCategory S
  let U := unit (RingedTensor.ringSheaf R)
  let UI := unit (RingedTensor.ringSheaf RI)
  let T := RingedTensor.tensorFunctor c
  let ε : L ≅ I.modules ⋙ T := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom c (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  have hq M : k.q M = RingedTensor.tensorUnit c (I.modules.obj M) ≫
      (RingedTensor.underlying S).map (ε.inv.app M) :=
    comparison_q_eq R S RI uInv I c L hobj k M
  have hqn {M N : SheafOfModules.{u} (RingedTensor.ringSheaf R)} (f : M ⟶ N) :
      (RingedTensor.underlying RI).map (I.modules.map f) ≫ k.q N =
        k.q M ≫ (RingedTensor.underlying S).map (L.map f) := by
    rw [hq, hq]
    have hn := congrArg ((RingedTensor.underlying RI).map)
      ((RingedTensor.tensorAdjunction c).unit.naturality (I.modules.map f))
    change (RingedTensor.underlying RI).map (I.modules.map f) ≫
      RingedTensor.tensorUnit c (I.modules.obj N) =
      RingedTensor.tensorUnit c (I.modules.obj M) ≫
        (RingedTensor.underlying S).map (T.map (I.modules.map f)) at hn
    have he : T.map (I.modules.map f) ≫ ε.inv.app N =
        ε.inv.app M ≫ L.map f := ε.inv.naturality f
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
      he, Functor.map_comp, Category.assoc]
  obtain ⟨eI, heI⟩ := inverseImage_unit_iso R RI uInv I
  obtain ⟨eS, heS⟩ := scalarExtension_unit_iso S RI c
  let j : L.obj U ≅ unit (RingedTensor.ringSheaf S) :=
    ε.app U ≪≫ T.mapIso eI.symm ≪≫ eS
  have hj : k.q U ≫ (RingedTensor.underlying S).map j.hom =
      (RingedTensor.underlying RI).map eI.inv ≫ RingedTensor.tensorUnit c UI ≫
        (RingedTensor.underlying S).map eS.hom := by
    rw [hq]
    have hε : ε.inv.app U ≫ j.hom = T.map eI.inv ≫ eS.hom := by
      simp only [j, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
        ← Category.assoc, ε.inv_hom_id_app, Category.id_comp]
    rw [Category.assoc, ← Functor.map_comp, hε, Functor.map_comp]
    have hn := congrArg ((RingedTensor.underlying RI).map)
      ((RingedTensor.tensorAdjunction c).unit.naturality eI.inv)
    change (RingedTensor.underlying RI).map eI.inv ≫ RingedTensor.tensorUnit c UI =
      RingedTensor.tensorUnit c (I.modules.obj U) ≫
        (RingedTensor.underlying S).map (T.map eI.inv) at hn
    rw [← Category.assoc, ← hn, Category.assoc]
  have heI' : (RingedTensor.underlying RI).map eI.inv =
      I.moduleUnderlying.hom.app U ≫ I.ringUnderlying.hom := by
    apply (cancel_epi ((RingedTensor.underlying RI).map eI.hom)).mp
    rw [← Functor.map_comp, Iso.hom_inv_id, (RingedTensor.underlying RI).map_id]
    erw [heI]
    change 𝟙 _ = I.ringUnderlying.inv ≫ (I.moduleUnderlying.app U).inv ≫
      (I.moduleUnderlying.app U).hom ≫ I.ringUnderlying.hom
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  refine ⟨j, ?_⟩
  intro M
  apply (cancel_epi (L.map (ρ_ M).inv)).mp
  rw [← L.map_comp, Iso.inv_hom_id, L.map_id]
  apply comparison_q_hom_ext R S RI uInv I c L hobj k M (L.obj M)
  let Z := (RingedTensor.underlying R).obj M
  let one : Z ⟶ (RingedTensor.underlying R).obj U :=
    ⟨{ app := fun W ↦ ↾(fun _ ↦ (1 : R.obj.obj W))
       naturality := by
         intro W V f
         ext x
         exact (map_one (R.obj.map f).hom).symm }⟩
  let z := (RingedTensor.underlying R).map (ρ_ M).inv
  have hz (W : Cᵒᵖ) (t : Z.obj.obj W) :
      z.hom.app W t = RingedTensor.pure R M U W t (1 : R.obj.obj W) := by
    have h : (ρ_ M).hom.val.app W
        (RingedTensor.pure R M U W t (1 : R.obj.obj W)) = t := by
      simpa only [one_smul] using pure_right_unitor R M W t 1
    have hi := congrArg ((ρ_ M).inv.val.app W) h
    have hc := congrArg (fun f ↦ f.val.app W
      (RingedTensor.pure R M U W t (1 : R.obj.obj W))) (ρ_ M).hom_inv_id
    exact hi.symm.trans hc
  ext W m
  let t := (I.moduleUnderlying.hom.app M).hom.app W m
  have ht : (I.moduleUnderlying.inv.app M).hom.app W t = m :=
    congrArg (fun f ↦ f.hom.app W m) (I.moduleUnderlying.hom_inv_id_app M)
  have hp := k.pure M U Z (𝟙 Z) one z hz W t
  have hn := congrArg (fun f ↦ f.hom.app W t)
    (I.moduleUnderlying.inv.naturality (ρ_ M).inv)
  have hu := congrArg (fun f ↦ f.hom.app W m) (hqn (ρ_ M).inv)
  have hj1 : j.hom.val.app W
      ((uInv.map one ≫ I.moduleUnderlying.inv.app U ≫ k.q U).hom.app W t) =
        (1 : S.obj.obj W) := by
    have hh := congrArg (fun f ↦ f.hom.app W
      ((uInv.map one ≫ I.moduleUnderlying.inv.app U).hom.app W t)) hj
    simp only [heI'] at hh
    have hcancel := congrArg (fun f ↦ f.hom.app W ((uInv.map one).hom.app W t))
      (I.moduleUnderlying.inv_hom_id_app U)
    have hOne := I.ringOne Z one (fun _ _ ↦ rfl) W t
    change j.hom.val.app W
      ((k.q U).hom.app W ((I.moduleUnderlying.inv.app U).hom.app W
        ((uInv.map one).hom.app W t))) = _
    change j.hom.val.app W
      ((k.q U).hom.app W ((I.moduleUnderlying.inv.app U).hom.app W
        ((uInv.map one).hom.app W t))) =
      eS.hom.val.app W ((RingedTensor.tensorUnit c UI).hom.app W
        (I.ringUnderlying.hom.hom.app W ((I.moduleUnderlying.hom.app U).hom.app W
          ((I.moduleUnderlying.inv.app U).hom.app W ((uInv.map one).hom.app W t))))) at hh
    change (I.moduleUnderlying.hom.app U).hom.app W
      ((I.moduleUnderlying.inv.app U).hom.app W ((uInv.map one).hom.app W t)) =
        (uInv.map one).hom.app W t at hcancel
    simp only [id_eq] at hOne
    refine hh.trans ((heS W _).trans ?_)
    exact (congrArg (c.hom.app W)
      ((congrArg (I.ringUnderlying.hom.hom.app W) hcancel).trans hOne)).trans (map_one _)
  have hp' : (k.mu M U).hom.val.app W
      ((L.map (ρ_ M).inv).val.app W ((k.q M).hom.app W m)) =
      RingedTensor.pure S (L.obj M) (L.obj U) W ((k.q M).hom.app W m)
        ((uInv.map one ≫ I.moduleUnderlying.inv.app U ≫ k.q U).hom.app W t) := by
    change (I.moduleUnderlying.inv.app (M ⊗ U)).hom.app W
        ((uInv.map z).hom.app W t) =
      (I.modules.map (ρ_ M).inv).val.app W
        ((I.moduleUnderlying.inv.app M).hom.app W t) at hn
    simp only [ht] at hn
    change (k.q (M ⊗ U)).hom.app W ((I.modules.map (ρ_ M).inv).val.app W m) =
      (L.map (ρ_ M).inv).val.app W ((k.q M).hom.app W m) at hu
    simp only [uInv.map_id] at hp
    change (k.mu M U).hom.val.app W
        ((k.q (M ⊗ U)).hom.app W
          ((I.moduleUnderlying.inv.app (M ⊗ U)).hom.app W ((uInv.map z).hom.app W t))) =
      RingedTensor.pure S (L.obj M) (L.obj U) W
        ((k.q M).hom.app W ((I.moduleUnderlying.inv.app M).hom.app W t))
        ((uInv.map one ≫ I.moduleUnderlying.inv.app U ≫ k.q U).hom.app W t) at hp
    simp only [ht, hn, hu] at hp
    exact hp
  change (ρ_ (L.obj M)).hom.val.app W
      ((𝟙 (L.obj M) ⊗ₘ j.hom).val.app W
        ((k.mu M U).hom.val.app W
          ((L.map (ρ_ M).inv).val.app W ((k.q M).hom.app W m)))) =
    (k.q M).hom.app W m
  simp only [hp', RingedTensor.pure_map]
  change (ρ_ (L.obj M)).hom.val.app W
    (RingedTensor.pure S (L.obj M) (unit (RingedTensor.ringSheaf S)) W
      ((k.q M).hom.app W m)
      (j.hom.val.app W
        ((uInv.map one ≫ I.moduleUnderlying.inv.app U ≫ k.q U).hom.app W t))) = _
  simp only [hj1, pure_right_unitor, one_smul]

end SheafOfModules
