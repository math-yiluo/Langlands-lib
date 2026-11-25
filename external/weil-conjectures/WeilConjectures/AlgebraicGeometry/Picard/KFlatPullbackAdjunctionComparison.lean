/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData

/-! # K-flat computation of the pinned adjunction on chain maps

## References

* Stacks Project, Cohomology, Tags 06YI, 06YJ, and 079W
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem counit_isIso {S S' : Scheme.{u}} (g : S' ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    [(Scheme.Modules.tensorPullback g).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (hε : (derivedPullback g).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso _ (.up ℤ)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) :
    IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, δ, hδ, _, hK⟩ :=
    (derivedPullback_spec g)
  have hF' : F = Scheme.Modules.tensorPullback g :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hmap a)
  subst F
  have := hε
  have : (derivedPullback g).IsLeftDerivedFunctor δ
      (HomotopyCategory.quasiIso _ (.up ℤ)) := hδ
  have := hK P hP
  let e := Functor.leftDerivedUnique (derivedPullback g) (derivedPullback g) ε δ
    (HomotopyCategory.quasiIso _ (.up ℤ))
  have he : e.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      δ.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    simp [e, Functor.leftDerivedNatIso]
  rw [← he]
  infer_instance

private noncomputable def kFlat_pullback_adjunction_comparison_iso
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    [hL : (Scheme.Modules.tensorPullback g).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (hεP : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) :
    (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).obj
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (derivedPullback g).obj (DerivedCategory.Q.obj P) := by
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)
  let uS := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (moduleRings S.toRingedSpace))
  let uT := DerivedCategory.quotientCompQhIso
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace))
  letI := hεP
  exact (uT.app (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    (asIso (ε.app (q.obj P))).symm ≪≫ (derivedPullback g).mapIso (uS.app P)

private theorem kFlat_pullback_adjunction_comparison_iso_inv
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    [hL : (Scheme.Modules.tensorPullback g).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    [hεP : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))] :
    (kFlat_pullback_adjunction_comparison_iso g ε P hεP).inv =
      ((derivedPullback g).mapIso
        ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings S.toRingedSpace))).app P)).inv ≫
        (asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).hom ≫
        (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace))).hom.app
          (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) := by
  simp [kFlat_pullback_adjunction_comparison_iso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv]

private theorem kFlat_pullback_adjunction_comparison_transpose
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    [hL : (Scheme.Modules.tensorPullback g).Additive]
    {P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
    {I : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ}
    {α : P ⟶ ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I} :
    (((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomotopyCategory
        (.up ℤ)).homEquiv _ _)
      ((HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) (.up ℤ)).map
        ((((Classical.choose
          (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomologicalComplex
            (.up ℤ)).homEquiv _ _).symm α)) =
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)).map α := by
  rw [Adjunction.homEquiv_apply]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)
  let ac := (Classical.choose
    (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomologicalComplex (.up ℤ)
  change q.map (ac.unit.app P) ≫ q.map
    (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).map ((ac.homEquiv P I).symm α)) = q.map α
  rw [← Functor.map_comp]
  exact congrArg q.map ((ac.homEquiv P I).apply_symm_apply α)

-- Keeping the counit and adjunction as parameters avoids unfolding their choices in rewrites.
private theorem kFlat_pullback_adjunction_comparison_naturality
    [d : ∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S)
    [hL : (Scheme.Modules.tensorPullback g).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback g ⟶
      (Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace)))
    (adj : derivedPullback g ⊣ schemeDerivedDirectImage g)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
    (α : P ⟶ ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
      (.up ℤ)).obj I)
    (a : ((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P ⟶ I)
    [hεP : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))]
    (h : adj.homEquiv _ _
        (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map a)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map α) ≫
        (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj I)) :
    (DerivedCategory.Q.{w}
      (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).map a =
      (kFlat_pullback_adjunction_comparison_iso g ε P hεP).hom ≫
        (adj.homEquiv _ _).symm
          (DerivedCategory.Q.map α ≫ (schemeMVDirectImageLocalization g).app I) := by
  let : HasDerivedCategory.{w} S.Modules := d S
  let : HasDerivedCategory.{w} S'.Modules := d S'
  apply (cancel_epi (kFlat_pullback_adjunction_comparison_iso g ε P hεP).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  rw [kFlat_pullback_adjunction_comparison_iso_inv]
  dsimp only [Functor.mapIso_inv]
  simp only [Category.assoc]
  erw [← DerivedCategory.quotientCompQhIso_hom_naturality a]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [asIso_hom]
  rw [← Category.assoc (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))]
  rw [Adjunction.homEquiv_naturality_right]
  erw [h]
  have hf : ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomotopyCategoryFactors
      (.up ℤ)).inv.app I = 𝟙 _ := rfl
  dsimp only [schemeMVDirectImageLocalization]
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.whiskerRight_app, hf, Category.assoc]
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the concrete sheaf adjunctions requires unfolding their chosen instances.
/-- For a K-flat source, the localized ordinary transpose computes the pinned derived
transpose. The comparison is independent of the target complex and the chain map. -/
theorem kFlat_pullback_adjunction_comparison
    [d : ∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {S S' : Scheme.{u}} (g : S' ⟶ S) :
    ∃ (_hL : (Scheme.Modules.tensorPullback g).Additive)
      (e : ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
        (_ : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P),
          (DerivedCategory.Q
              (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).obj
              (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) ≅
            (derivedPullback g).obj (DerivedCategory.Q.obj P)),
      ∀ (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
        (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P)
        (I : CochainComplex (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) ℤ)
        (α : P ⟶ ((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj I),
        (DerivedCategory.Q
            (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).map
            ((((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction g)).mapHomologicalComplex
                (.up ℤ)).homEquiv _ _).symm α) =
          (e P hP).hom ≫ ((relativeMVAdj g).homEquiv _ _).symm
            (DerivedCategory.Q.map α ≫ (schemeMVDirectImageLocalization g).app I) := by
  classical
  let : HasDerivedCategory.{w} S.Modules := d S
  let : HasDerivedCategory.{w} S'.Modules := d S'
  let hL := @Classical.choose _ _ (@exists_derivedPullbackComposition.{u, w} d)
  let ε := (Classical.choose (Classical.choose_spec (exists_derivedPullbackComposition))) g
  have hε := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_derivedPullbackComposition)))) g
  have : (Scheme.Modules.tensorPullback g).Additive := hL g
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (.up ℤ)
  let q' := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) (.up ℤ)
  have hεP (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) : IsIso (ε.app (q.obj P)) :=
    counit_isIso g ε hε P hP
  let e (P : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsAcyclicTensorKFlat (R := S.sheaf) P) :
      (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings S'.toRingedSpace))).obj
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) ≅
          (derivedPullback g).obj (DerivedCategory.Q.obj P) :=
    kFlat_pullback_adjunction_comparison_iso g ε P (hεP P hP)
  let A := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  refine ⟨hL g, e, ?_⟩
  intro P hP I α
  let ac := A.mapHomologicalComplex (.up ℤ)
  let a := (ac.homEquiv _ _).symm α
  let hεP_inst : IsIso (ε.app (q.obj P)) := hεP P hP
  apply kFlat_pullback_adjunction_comparison_naturality g ε (relativeMVAdj g) P I α a
  have h := Classical.choose_spec (exists_schemeDerivedAdjunction g ε hε)
    (q.obj P) (q'.obj I) (q'.map a)
  have ha := kFlat_pullback_adjunction_comparison_transpose (g := g) (P := P) (I := I)
    (α := α)
  exact h.trans (congrArg (fun f ↦ DerivedCategory.Qh.map f ≫
    (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      (q'.obj I)) ha)

end AlgebraicGeometry
