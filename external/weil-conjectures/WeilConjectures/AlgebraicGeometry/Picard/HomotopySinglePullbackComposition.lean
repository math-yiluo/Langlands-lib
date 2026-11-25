/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Composition of the tensor-to-ordinary comparison on homotopy single complexes

## References

* Stacks Project, Tag 0D5S, and uniqueness of adjoints
* Stacks Project, Tag 0D5S, and the adjunction mate formula for pullback composition
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

private theorem uniq
    {A B : Type*} [Category A] [Category B] {F F' : A ⥤ B} {G : B ⥤ A}
    (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]
private theorem compat
    {A B C : Type*} [Category A] [Category B] [Category C]
    {Tf Pf : B ⥤ C} {Tg Pg : A ⥤ B} {Tfg Pfg : A ⥤ C}
    {Rf : C ⥤ B} {Rg : B ⥤ A} {Rfg : C ⥤ A}
    (af : Tf ⊣ Rf) (bf : Pf ⊣ Rf) (ag : Tg ⊣ Rg) (bg : Pg ⊣ Rg)
    (afg : Tfg ⊣ Rfg) (bfg : Pfg ⊣ Rfg)
    (p : Pg ⋙ Pf ≅ Pfg) (q : Rf ⋙ Rg ≅ Rfg)
    (hp : conjugateEquiv (bg.comp bf) bfg p.inv = q.hom) :
    Functor.whiskerRight (ag.leftAdjointUniq bg).hom Tf ≫
      Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom ≫ p.hom =
      ((conjugateIsoEquiv afg (ag.comp af)).symm q.symm).hom ≫
        (afg.leftAdjointUniq bfg).hom := by
  have hp' : conjugateEquiv bfg (bg.comp bf) p.hom = q.inv := by
    have h := conjugateEquiv_comm (bg.comp bf) bfg p.hom_inv_id
    rw [hp] at h
    simpa using (Iso.eq_inv_comp q).2 h
  apply (conjugateEquiv bfg (ag.comp af)).injective
  rw [← conjugateEquiv_comp bfg (bg.comp af) (ag.comp af)
    (Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom ≫ p.hom)
    (Functor.whiskerRight (ag.leftAdjointUniq bg).hom Tf)]
  rw [← conjugateEquiv_comp bfg (bg.comp bf) (bg.comp af)
    p.hom (Functor.whiskerLeft Pg (af.leftAdjointUniq bf).hom)]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft]
  simp only [uniq, hp']
  simp only [Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.comp_id]
  rw [← conjugateEquiv_comp bfg afg (ag.comp af)]
  simp only [uniq, Category.id_comp, conjugateIsoEquiv_symm_apply_hom,
    Equiv.apply_symm_apply, Iso.symm_hom]

private theorem single_compat
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ F') (b : G ⟶ G') (d : H ⟶ H')
    (c : F ⋙ G ≅ H) (p : F' ⋙ G' ≅ H')
    (h : Functor.whiskerRight a G ≫ Functor.whiskerLeft F' b ≫ p.hom = c.hom ≫ d)
    (N : A) :
    (Functor.mapHomologicalComplexCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj N) ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (d.app N) =
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N ≫
        (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (a.app N)) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F'.obj N) ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (b.app (F'.obj N)) ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (p.hom.app N) := by
  apply HomologicalComplex.to_single_hom_ext
  have hn := congrArg (fun α ↦ α.app N) h
  simpa [HomologicalComplex.singleMapHomologicalComplex,
    HomologicalComplex.single, Functor.mapHomologicalComplexCompIso,
    NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex,
    Functor.mapHomologicalComplex, Category.assoc] using hn.symm

private theorem homotopy_single_compat
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Limits.HasZeroObject A] [Limits.HasZeroObject B] [Limits.HasZeroObject C]
    {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ F') (b : G ⟶ G') (d : H ⟶ H')
    (c : F ⋙ G ≅ H) (p : F' ⋙ G' ≅ H')
    (h : Functor.whiskerRight a G ≫ Functor.whiskerLeft F' b ≫ p.hom = c.hom ≫ d)
    (N : A) :
    let r_f := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app
        (F'.obj N)) ≫ (HomotopyCategory.singleFunctor C 0).map (b.app (F'.obj N))
    let r_g := (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomotopyCategory.singleFunctor B 0).map (a.app N)
    let r_fg := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomotopyCategory.singleFunctor C 0).map (d.app N)
    (Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor A 0).obj N) ≫ r_fg =
      (G.mapHomotopyCategory (ComplexShape.up ℤ)).map r_g ≫ r_f ≫
        (HomotopyCategory.singleFunctor C 0).map (p.hom.app N) := by
  have hs := single_compat a b d c p h N
  have hq := congrArg
    (fun k ↦ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map k) hs
  simpa only [Functor.map_comp, Functor.mapHomotopyCategory_map,
    HomotopyCategory.singleFunctor, HomotopyCategory.singleFunctors,
    SingleFunctors.postcomp, CochainComplex.singleFunctors, Functor.comp_map,
    Functor.comp_obj, Functor.mapHomotopyCategoryCompIso,
    Quotient.natIsoLift_hom, Functor.isoWhiskerRight_hom, Quotient.natTransLift,
    Functor.whiskerRight_app, HomotopyCategory.quotient_obj_as, Category.assoc] using hq

/-- The termwise tensor-to-ordinary single-complex comparison respects composition. -/
theorem homotopySinglePullbackComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Modules)
    [(tensorPullback f).Additive] [(tensorPullback g).Additive]
    [(tensorPullback (f ≫ g)).Additive] :
    let t_f := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (pullbackPushforwardAdjunction f)
    let t_g := (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
      (pullbackPushforwardAdjunction g)
    let t_fg := (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g))).leftAdjointUniq
      (pullbackPushforwardAdjunction (f ≫ g))
    let r_f := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app ((pullback g).obj N)) ≫
      (HomotopyCategory.singleFunctor X.Modules 0).map
        (t_f.hom.app ((pullback g).obj N))
    let r_g := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback g) (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomotopyCategory.singleFunctor Y.Modules 0).map (t_g.hom.app N)
    let r_fg := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback (f ≫ g)) (ComplexShape.up ℤ) 0).hom.app N) ≫
      (HomotopyCategory.singleFunctor X.Modules 0).map (t_fg.hom.app N)
    (Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (exists_tensorPullbackAdjunction f)))).symm
        (pushforwardComp f g).symm)
      (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.singleFunctor Z.Modules 0).obj N) ≫ r_fg =
    ((tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map r_g ≫ r_f ≫
      (HomotopyCategory.singleFunctor X.Modules 0).map
        ((pullbackComp f g).hom.app N) := by
  let a_f := Classical.choose (exists_tensorPullbackAdjunction f)
  let a_g := Classical.choose (exists_tensorPullbackAdjunction g)
  let a_fg := Classical.choose (exists_tensorPullbackAdjunction (f ≫ g))
  let b_f := pullbackPushforwardAdjunction f
  let b_g := pullbackPushforwardAdjunction g
  let b_fg := pullbackPushforwardAdjunction (f ≫ g)
  let t_f := a_f.leftAdjointUniq b_f
  let t_g := a_g.leftAdjointUniq b_g
  let t_fg := a_fg.leftAdjointUniq b_fg
  let c := (conjugateIsoEquiv a_fg (a_g.comp a_f)).symm (pushforwardComp f g).symm
  have hu := compat a_f b_f a_g b_g a_fg b_fg
    (pullbackComp f g) (pushforwardComp f g) (conjugateEquiv_pullbackComp_inv f g)
  exact homotopy_single_compat t_g.hom t_f.hom t_fg.hom c (pullbackComp f g) hu N

end AlgebraicGeometry.Scheme.Modules
