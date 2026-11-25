/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Homology.OpenCoverMateModuleShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # The complex-level open-cover sequence with its canonical mate maps

Source: Stacks Project, Tag 08BU, proof, and Tag 08BW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

private lemma nestedTranspose_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (RU : C ⥤ D) (RW : C ⥤ E) (T : D ⥤ E)
    (SU : D ⥤ C) (SW : E ⥤ C)
    (aU : SU ⊣ RU) (aW : SW ⊣ RW) (c : RU ⋙ T ≅ RW) (F : C) :
    (aW.homEquiv _ _).symm
        (c.inv.app F ≫ T.map (aU.unit.app (RU.obj F)) ≫
          c.hom.app (SU.obj (RU.obj F))) ≫ aU.counit.app F = aW.counit.app F := by
  apply (aW.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_unit, aW.right_triangle_components]
  simp only [Category.assoc]
  rw [← c.hom.naturality]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rw [aU.right_triangle_components]
  simp

private noncomputable def nestedMate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (RU : C ⥤ D) (RW : C ⥤ E) (T : D ⥤ E)
    (SU : D ⥤ C) (SW : E ⥤ C)
    (aU : SU ⊣ RU) (aW : SW ⊣ RW) (c : RU ⋙ T ≅ RW) :
    RW ⋙ SW ⟶ RU ⋙ SU := by
  let t : RW ⟶ (RU ⋙ SU) ⋙ RW :=
    c.inv ≫ Functor.whiskerRight (Functor.whiskerLeft RU aU.unit) T ≫
      (Functor.associator RU SU (RU ⋙ T)).inv ≫ Functor.whiskerLeft (RU ⋙ SU) c.hom
  exact
    { app := fun F ↦ (aW.homEquiv _ _).symm (t.app F)
      naturality := fun {F G} f ↦
        aW.homEquiv_naturality_right_square (RW.map f) (t.app G) (t.app F)
          ((RU ⋙ SU).map f) (t.naturality f) }

private lemma nestedMate_app
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (RU : C ⥤ D) (RW : C ⥤ E) (T : D ⥤ E)
    (SU : D ⥤ C) (SW : E ⥤ C)
    (aU : SU ⊣ RU) (aW : SW ⊣ RW) (c : RU ⋙ T ≅ RW) (F : C) :
    (nestedMate RU RW T SU SW aU aW c).app F =
      (aW.homEquiv _ _).symm
        (c.inv.app F ≫ T.map (aU.unit.app (RU.obj F)) ≫
          c.hom.app (SU.obj (RU.obj F))) := by
  simp [nestedMate]

set_option backward.isDefEq.respectTransparency false in
/-- The termwise open-cover short exact sequence, before localization.

Source: Stacks Project, Tag 08BU, proof, and Tag 08BW (nested restriction maps).
(blueprint: lem-sc-open-cover-mate-complex-short-exact).

Proof: First use the actual extension-by-zero functors, namely the direct-sum
extension presheaf followed by module sheafification. For W contained in U, the
extension map from W to U is the unique map whose composite with the U counit is
the W counit. On sections its transpose is restriction to W of the U unit,
conjugated by `overFunctorMap`. These maps are natural in the module, hence commute
with the differentials of K and give complex maps. Take their difference into the
biproduct; the second map is the pair of counits. Their composite is zero since
both component composites are the W counit. At a point in U intersection V the
stalk sequence is diagonal difference followed by addition; in U minus V or V
minus U it is the identity sequence with zero at one end. The cover excludes a
fourth case. These sequences are short exact, so stalkwise reflection of exactness
and of monomorphisms and epimorphisms proves short exactness in every degree.
Degreewise short exactness is short exactness of complexes. Finally transport
along the unique compatible isomorphisms from any chosen left adjoints to these
extension-by-zero functors. These isomorphisms commute with units and counits,
so they preserve the displayed mate formulas and the short exact sequence. Empty
opens and equal opens satisfy the same stalk calculation. No derived objects or
distinguished triangles occur in this statement. -/
theorem open_cover_mate_complex_shortExact (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    let KU := (SU.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let KV := (SV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let KW := (SW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let εU := (aU.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
    let εV := (aV.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    ∃ (f : KW ⟶ KU ⊞ KV),
      (∀ n, (f ≫ biprod.fst).f n = (aW.homEquiv _ _).symm
        (cU.inv.app (K.X n) ≫
          (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
            (aU.unit.app ((overFunctor.{u} R U).obj (K.X n))) ≫
          cU.hom.app (SU.obj ((overFunctor.{u} R U).obj (K.X n))))) ∧
      (∀ n, (-(f ≫ biprod.snd)).f n = (aW.homEquiv _ _).symm
        (cV.inv.app (K.X n) ≫
          (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
            (aV.unit.app ((overFunctor.{u} R V).obj (K.X n))) ≫
          cV.hom.app (SV.obj ((overFunctor.{u} R V).obj (K.X n))))) ∧
      ∃ hz : f ≫ biprod.desc εU εV = 0,
        (ShortComplex.mk f (biprod.desc εU εV) hz).ShortExact := by
  let KU := (SU.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((overFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let KV := (SV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((overFunctor.{u} R V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let KW := (SW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((overFunctor.{u} R (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let εU := (aU.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
  let εV := (aV.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
  let tU := nestedMate (overFunctor.{u} R U) (overFunctor.{u} R (U ⊓ V))
    (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)) SU SW aU aW
    (overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))
  let tV := nestedMate (overFunctor.{u} R V) (overFunctor.{u} R (U ⊓ V))
    (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)) SV SW aV aW
    (overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))
  let iU : KW ⟶ KU :=
    { f := fun n ↦ tU.app (K.X n)
      comm' := fun i j _ ↦ (tU.naturality (K.d i j)).symm }
  let iV : KW ⟶ KV :=
    { f := fun n ↦ tV.app (K.X n)
      comm' := fun i j _ ↦ (tV.naturality (K.d i j)).symm }
  let εW := (aW.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
  have hcU : iU ≫ εU = εW := by
    apply HomologicalComplex.Hom.ext
    funext n
    change tU.app (K.X n) ≫ aU.counit.app (K.X n) = aW.counit.app (K.X n)
    rw [nestedMate_app]
    exact nestedTranspose_counit _ _ _ _ _ aU aW _ (K.X n)
  have hcV : iV ≫ εV = εW := by
    apply HomologicalComplex.Hom.ext
    funext n
    change tV.app (K.X n) ≫ aV.counit.app (K.X n) = aW.counit.app (K.X n)
    rw [nestedMate_app]
    exact nestedTranspose_counit _ _ _ _ _ aV aW _ (K.X n)
  refine ⟨biprod.lift iU (-iV), ?_, ?_, ?_⟩
  · intro n
    simpa only [biprod.lift_fst] using
      nestedMate_app _ _ _ _ _ aU aW _ (K.X n)
  · intro n
    simpa only [biprod.lift_snd, neg_neg] using
      nestedMate_app _ _ _ _ _ aV aW _ (K.X n)
  · have hz : biprod.lift iU (-iV) ≫ biprod.desc εU εV = 0 := by
      simp only [biprod.lift_desc, Preadditive.neg_comp, hcU, hcV, add_neg_cancel]
    have hdegree (n : ℤ) : ∃ hzn :
        biprod.lift (iU.f n) (-(iV.f n)) ≫
          biprod.desc (εU.f n) (εV.f n) = 0,
        (ShortComplex.mk (biprod.lift (iU.f n) (-(iV.f n)))
          (biprod.desc (εU.f n) (εV.f n)) hzn).ShortExact := by
      have hU : iU.f n ≫ εU.f n = εW.f n :=
        congrArg (fun f : KW ⟶ K ↦ f.f n) hcU
      have hV : iV.f n ≫ εV.f n = εW.f n :=
        congrArg (fun f : KW ⟶ K ↦ f.f n) hcV
      have hzn : biprod.lift (iU.f n) (-(iV.f n)) ≫
          biprod.desc (εU.f n) (εV.f n) = 0 := by
        simp only [biprod.lift_desc, Preadditive.neg_comp, hU, hV, add_neg_cancel]
      refine ⟨hzn, ?_⟩
      dsimp only [KU, KV, KW, Functor.mapHomologicalComplex]
      simpa only [iU, iV, tU, tV, nestedMate_app, KU, KV, KW, εU, εV,
        Functor.mapHomologicalComplex_obj_X, Functor.id_obj,
        Adjunction.mapHomologicalComplex_counit_app_f] using
        open_cover_mate_module_shortExact X R hR U V hcover SU SV SW aU aV aW (K.X n) hzn
    refine ⟨hz, ?_⟩
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    obtain ⟨hzn, hn⟩ := hdegree n
    let E := HomologicalComplex.eval (SheafOfModules.{u} R) (ComplexShape.up ℤ) n
    let e := E.mapBiprod KU KV
    apply ShortComplex.shortExact_of_iso _ hn
    refine ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_
    · change E.map (biprod.lift iU (-iV)) =
        biprod.lift (E.map iU) (-(E.map iV)) ≫ e.inv
      simpa only [Functor.map_neg] using
        (biprod.lift_mapBiprod E KU KV iU (-iV)).symm
    · change e.inv ≫ E.map (biprod.desc εU εV) =
        biprod.desc (E.map εU) (E.map εV)
      exact biprod.mapBiprod_inv_map_desc E KU KV εU εV

end SheafOfModules
