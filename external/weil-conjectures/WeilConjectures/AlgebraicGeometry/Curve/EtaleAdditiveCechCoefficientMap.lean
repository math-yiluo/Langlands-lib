/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization

/-! # The fixed additive coefficient maps before totalization

Source: Stacks Project, Tags 03P2 and 01EQ.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The lifted ordinary unit Cech complex, before the resolution augmentation.
Source: Stacks Project, Tag 03P2, ordinary coefficient Cech complex.
(blueprint: lem-pbc-additive-cech-coefficient-horizontal) -/
noncomputable abbrev additiveCechCoefficientComplex {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) :=
  (((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex (.up ℕ)).obj
      (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)))

/-- The prescribed coefficient augmentation into resolution degree zero.
This is the product of the actual section coordinates and I.ι.f 0.
Source: Stacks Project, Tag 01EQ, beta augmentation.
(blueprint: lem-pbc-additive-cech-coefficient-horizontal) -/
noncomputable def additiveCechCoefficientMap {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    (additiveCechCoefficientComplex U).X n ⟶
      ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).flip.X
        0).X n :=
    Pi.lift (fun y : Fin (n + 1) → ι ↦ AddCommGrpCat.ofHom
      { toFun := fun x ↦ (I.ι.f 0).hom.app
          (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
          (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
            (TopCat.Presheaf.cechComplexFunctorπ U
              (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))
        map_zero' := by
          simp only [ULift.zero_down, map_zero]
          change ((I.ι.f 0).hom.app _) 0 = 0
          exact map_zero _
        map_add' := by
          intro x y
          simp only [ULift.add_down, map_add]
          change ((I.ι.f 0).hom.app _) (_ + _) = _
          exact map_add _ _ _ })

/-- The fixed coordinate maps commute with the horizontal Cech differential.
Source: Stacks Project, Tag 03P2, the natural structure-section coordinates;
Tag 01EQ, Lemma 20.11.2, naturality of beta.
(blueprint: lem-pbc-additive-cech-coefficient-horizontal)

Proof: Project both sides to any tuple of m+1 opens. Expand the alternating
Cech differential into its cofaces. For each deleted index, naturality of
restrictFunctorΓ.inv identifies the restriction of a unit section with the
restriction of the corresponding regular function on the open subscheme.
The structural scalar restriction along toSpecΓ agrees with that restriction.
Naturality of I.ι.f 0 then commutes this restriction past the augmentation.
These coordinate equalities give equality for each coface, hence for their
signed sum, because all maps are additive and ULift preserves addition.
Outside adjacent degrees both differentials are zero. Products indexed by an
empty tuple family are zero objects; repeated or empty opens obey the same
naturality identities. No affine or covering hypothesis is used. -/
theorem additiveCechCoefficientMap_comm {X : Scheme.{u}} {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf)
    (n m : ℕ) :
    additiveCechCoefficientMap U I n ≫
        ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).flip.X
          0).d n m =
      (additiveCechCoefficientComplex U).d n m ≫ additiveCechCoefficientMap U I m := by
  classical
  let T := forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  let P := presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)
  let i := additiveCechOpenInclusion X
  let ρ : P ⋙ T ⟶ i.op ⋙ X.etaleAdditiveSheaf.obj :=
    { app W := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up ((X.restrictFunctorΓ.inv.app W).hom x.down)
          map_zero' := by
            apply ULift.ext
            change (X.restrictFunctorΓ.inv.app W).hom 0 = 0
            exact map_zero _
          map_add' := by
            intro x y
            apply ULift.ext
            change (X.restrictFunctorΓ.inv.app W).hom (x.down + y.down) = _
            exact map_add _ _ _ }
      naturality W V f := by
        ext x
        apply ULift.ext
        change (X.restrictFunctorΓ.inv.app V).hom ((X.presheaf.map f).hom x.down) =
          (Scheme.Γ.map ((X.restrictFunctor.map f.unop).left).op).hom
            ((X.restrictFunctorΓ.inv.app W).hom x.down)
        exact ConcreteCategory.congr_hom (X.restrictFunctorΓ.inv.naturality f) x.down }
  let σ := ρ ≫ Functor.whiskerLeft i.op (I.ι.f 0).hom
  let e : (T.mapHomologicalComplex (.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj (P ⋙ T) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun k ↦ PreservesProduct.iso T
        (fun y : Fin (k + 1) → ι ↦ P.obj (op (∏ᶜ fun l ↦ U (y l))))) (by
        rintro k _ rfl
        apply Pi.hom_ext
        intro y
        change Fin (k + 2) → ι at y
        simp only [Category.assoc, PreservesProduct.iso_hom]
        change piComparison T _ ≫ ((cechComplexFunctor U).obj (P ⋙ T)).d k (k + 1) ≫
            TopCat.Presheaf.cechComplexFunctorπ U (P ⋙ T) (k + 1) y =
          T.map (((cechComplexFunctor U).obj P).d k (k + 1)) ≫ piComparison T _ ≫
            TopCat.Presheaf.cechComplexFunctorπ U (P ⋙ T) (k + 1) y
        rw [TopCat.Presheaf.cechComplexFunctor_d_π]
        simp only [TopCat.Presheaf.cechComplexFunctorπ]
        erw [piComparison_comp_π]
        rw [← T.map_comp]
        erw [TopCat.Presheaf.cechComplexFunctor_d_π]
        simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
          Preadditive.comp_zsmul]
        apply Finset.sum_congr rfl
        intro a _
        erw [← Category.assoc, piComparison_comp_π]
        rw [T.map_comp]
        rfl)
  let c := e.hom ≫ (cechComplexFunctor U).map σ
  have hc (k : ℕ) : c.f k = additiveCechCoefficientMap U I k := by
    apply Pi.hom_ext
    intro y
    change (e.hom.f k ≫ ((cechComplexFunctor U).map σ).f k) ≫
      TopCat.Presheaf.cechComplexFunctorπ U (i.op ⋙ (I.cocomplex.X 0).obj) k y = _
    rw [Category.assoc, TopCat.Presheaf.cechComplexFunctor_map_f_π]
    change piComparison T _ ≫
      (TopCat.Presheaf.cechComplexFunctorπ U (P ⋙ T) k y ≫ σ.app _) = _
    rw [← Category.assoc]
    erw [piComparison_comp_π, Pi.lift_comp_π]
    rfl
  change additiveCechCoefficientMap U I n ≫
      ((cechComplexFunctor U).obj (i.op ⋙ (I.cocomplex.X 0).obj)).d n m =
    ((T.mapHomologicalComplex (.up ℕ)).obj ((cechComplexFunctor U).obj P)).d n m ≫
      additiveCechCoefficientMap U I m
  simpa only [hc] using c.comm n m


/-- The resolution differential kills the fixed coefficient augmentation.
Source: Stacks Project, Tag 01EQ, the augmented resolution is a complex.
(blueprint: lem-pbc-additive-cech-coefficient-horizontal) -/
theorem additiveCechCoefficientMap_vertical {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ) :
    additiveCechCoefficientMap U I n ≫
        ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X n).d
          0 1 = 0 := by
  apply Pi.hom_ext
  intro y
  change (Pi.lift _ ≫ Limits.Pi.map (fun y : Fin (n + 1) → ι ↦
    (I.cocomplex.d 0 1).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))) ≫ _ = _
  erw [Category.assoc, Limits.Pi.map_π, ← Category.assoc, Pi.lift_comp_π]
  ext x
  have h := congrArg (fun f ↦ f.hom.app
    (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)))))
      I.ι_f_zero_comp_complex_d
  change (I.ι.f 0).hom.app _ ≫ (I.cocomplex.d 0 1).hom.app _ = 0 at h
  have hx := ConcreteCategory.congr_hom h
    (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
      (TopCat.Presheaf.cechComplexFunctorπ U
        (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))
  simp only [ConcreteCategory.comp_apply, zero_comp, AddCommGrpCat.zero_apply]
  change (I.cocomplex.d 0 1).hom.app
    (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
    ((I.ι.f 0).hom.app
      (op ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))))
    (ULift.up ((X.restrictFunctorΓ.inv.app (op (∏ᶜ fun l ↦ U (y l)))).hom
      (TopCat.Presheaf.cechComplexFunctorπ U
        (presheafOver X.toSpecΓ (SheafOfModules.unit X.ringCatSheaf)) n y x.down)))) = 0
  simpa only [ConcreteCategory.comp_apply, AddCommGrpCat.zero_apply] using hx

end AlgebraicGeometry.Scheme.Modules
