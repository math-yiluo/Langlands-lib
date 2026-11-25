/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.Algebra.Homology.AffineTildeDerivedTensorMate
import WeilConjectures.Algebra.Homology.AffineTildePushforwardHomologyFactorization
import WeilConjectures.Algebra.Homology.AffineTildeCoefficientPushforwardHomologyCoordinates

/-! # Homology coordinates of the raw affine tensor comparison

Source: Stacks Project, Tags 0DJ8, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-derived-tensor-homology-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) recoveryCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) recoveryCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) recoveryCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  affineTildePushforwardComparison
  affinePushforwardCohomologyMapOfComparison

section ExactFunctor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (K : CochainComplex C ℤ) (i : ℤ)

omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma complexHomologyIso_hom (L : CochainComplex C ℤ) :
    (F.mapHomologicalComplexHomologyIso (.up ℤ) i).hom.app L =
      ((L.sc i).mapHomologyIso F).hom := by
  simp only [Functor.comp_obj, Functor.mapHomologicalComplexHomologyIso,
    Functor.mapHomologicalComplexCompShortComplexFunctorIso, Functor.isoWhiskerRight_refl,
    ShortComplex.homologyFunctorIso, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    HomologicalComplex.homologyFunctorIso_hom_app, Functor.associator_inv_app,
    Functor.associator_hom_app, NatIso.ofComponents_hom_app, Functor.whiskerRight_app,
    HomologicalComplex.homologyFunctorIso_inv_app, Category.id_comp]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private lemma complexHomologyIso_inv (L : CochainComplex C ℤ) :
    (F.mapHomologicalComplexHomologyIso (.up ℤ) i).inv.app L =
      ((L.sc i).mapHomologyIso F).inv := by
  apply (cancel_mono ((L.sc i).mapHomologyIso F).hom).1
  erw [← complexHomologyIso_hom F i L, Iso.inv_hom_id_app,
    complexHomologyIso_hom F i L, Iso.inv_hom_id]

@[reassoc]
private lemma exactDerivedHomology (X : DerivedCategory C) (S : C)
    (a : S ⟶ (DerivedCategory.homologyFunctor C i).obj X)
    (f : X ⟶ DerivedCategory.Q.obj K) :
    F.map a ≫ (F.mapDerivedCategoryHomologyFunctorIso i).hom.app X ≫
        (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategory.map f) ≫
        (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategoryFactors.hom.app K) =
      F.map (a ≫ (DerivedCategory.homologyFunctor C i).map f ≫
        (DerivedCategory.homologyFunctorFactors C i).hom.app K) ≫
      ((K.sc i).mapHomologyIso F).inv ≫
      (DerivedCategory.homologyFunctorFactors D i).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  erw [← (F.mapDerivedCategoryHomologyFunctorIso i).hom.naturality_assoc f]
  dsimp only [Functor.comp_map]
  rw [F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← (DerivedCategory.homologyFunctor D i).map_comp, Iso.inv_hom_id_app]
  rw [complexHomologyIso_inv F i K]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasDerivedCategory C] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
@[reassoc]
private lemma exactComplexHomology (L : CochainComplex C ℤ) (S : C)
    (a : S ⟶ K.homology i) (k : K ⟶ L) :
    F.map a ≫ ((K.sc i).mapHomologyIso F).inv ≫
        (DerivedCategory.homologyFunctorFactors D i).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (DerivedCategory.homologyFunctor D i).map
          (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map k)) =
      F.map (a ≫ HomologicalComplex.homologyMap k i) ≫
        ((L.sc i).mapHomologyIso F).inv ≫
        (DerivedCategory.homologyFunctorFactors D i).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj L) := by
  erw [← (DerivedCategory.homologyFunctorFactors D i).inv.naturality
    ((F.mapHomologicalComplex (.up ℤ)).map k)]
  erw [← ShortComplex.mapHomologyIso_inv_naturality_assoc
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map k) F]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end ExactFunctor

@[reassoc]
private lemma homology_natIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [F.PreservesHomology] [G.PreservesHomology]
    (e : F ≅ G) (K : CochainComplex C ℤ) (i : ℤ) :
    ((K.sc i).mapHomologyIso F).inv ≫
        HomologicalComplex.homologyMap ((e.hom.mapHomologicalComplex (.up ℤ)).app K) i =
      e.hom.app (K.homology i) ≫ ((K.sc i).mapHomologyIso G).inv := by
  change ((K.sc i).mapHomologyIso F).inv ≫
    ShortComplex.homologyMap ((K.sc i).mapNatTrans e.hom) = _
  rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  rfl

private lemma coefficientHomology
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) (J : C ⥤ E)
    [F.Additive] [G.Additive] [J.Additive]
    [F.PreservesHomology] [G.PreservesHomology] [J.PreservesHomology]
    [(F ⋙ G).PreservesHomology]
    (e : F ⋙ G ≅ J) (X : CochainComplex D ℤ)
    (Y Z : CochainComplex C ℤ) (v : X ⟶ (F.mapHomologicalComplex (.up ℤ)).obj Y)
    (z : Y ⟶ Z) (i : ℤ) :
    ((X.sc i).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap ((G.mapHomologicalComplex (.up ℤ)).map v) i ≫
        HomologicalComplex.homologyMap ((e.hom.mapHomologicalComplex (.up ℤ)).app Y) i ≫
        HomologicalComplex.homologyMap ((J.mapHomologicalComplex (.up ℤ)).map z) i =
      G.map (HomologicalComplex.homologyMap v i ≫ ((Y.sc i).mapHomologyIso F).hom) ≫
        e.hom.app (Y.homology i) ≫ J.map (HomologicalComplex.homologyMap z i) ≫
        ((Z.sc i).mapHomologyIso J).inv := by
  erw [← ShortComplex.mapHomologyIso_inv_naturality_assoc
    ((HomologicalComplex.shortComplexFunctor D (.up ℤ) i).map v) G]
  have hc := mapHomologyIso_inv_comp (Y.sc i) F G
  have hc' : (((Y.sc i).map F).mapHomologyIso G).inv =
      G.map ((Y.sc i).mapHomologyIso F).hom ≫
        ((Y.sc i).mapHomologyIso (F ⋙ G)).inv := by
    rw [hc]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  erw [hc', Category.assoc, homology_natIso_assoc (F ⋙ G) J e Y i]
  erw [← ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) i).map z) J]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

@[reassoc]
private lemma homologyFactorsh
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctorFactorsh C i).hom.app
        ((HomotopyCategory.quotient _ _).obj K) ≫
      (HomotopyCategory.homologyFunctorFactors C (.up ℤ) i).hom.app K =
    (DerivedCategory.homologyFunctorFactors C i).hom.app K := by
  rw [DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Functor.comp_obj, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Applying homology to the raw tensor counit gives precisely the module
comparison, coefficient homology map and normalized ordinary pushforward map.
This statement contains no geometric base-change map or pullback representative.
Source: Stacks Project, Tags 06Y6, 06Z0, 0AVW and 0DJ8, equation-bc.
(blueprint: lem-pc-affine-tilde-derived-tensor-homology-coordinates).

Proof: Expand affineTildeDerivedTensorSourceIso. Naturality of the exact-tilde
homology isomorphism moves m.counit past this comparison. On the localized
ordinary scalar-extension complex its comparison is the composite of the exact
homology isomorphism and the Q/homology isomorphism. Substitute m.comparison_eq
for the counit followed by m.ordinaryIso. Apply functoriality of homology to the
remaining factors of affineTildeTensorCoefficientComplexMap. Naturality of exact
restriction-of-scalars homology moves its isomorphism past ordinaryToLocalized;
compatibility with composition of exact functors cancels the intermediate
restriction comparisons. The homology of the identity-on-carriers scalar iso
is rho.inv on homology, and that of the equality transport is z0. Naturality of
exact tilde moves these maps past its homology comparison. The remaining
Q/homology comparison, termwise affine pushforward comparison and derived unit
are exactly affineTildePushforwardCohomologyMap. Reassociate to obtain the stated
identity. This uses no K-flatness, quasi-coherence, boundedness or invertibility
of the module comparison. The zero complex and zero rings are included. -/
theorem affineTildeDerivedTensorToPushforward_homology
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A B M D)
    (φ : A →+* D) (ψ : B →+* D)
    (hφ : (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B)) = φ)
    (hψ : (algebraMap (A ⊗[R] B) D).comp
      Algebra.TensorProduct.includeRight.toRingHom = ψ) (i : ℤ) :
    let α := algebraMap (A ⊗[R] B) D
    let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
    let T := tilde.functor (.of B)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
    let s := (ModuleCat.restrictScalars j).map cE ≫ ρ.inv.app (C.homology i)
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} D) (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφ] : C = Cg))
    (affineTildeDerivedTensorSourceIso R A B D M m i).hom ≫
        H.map (affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ) =
      T.map s ≫ T.map ((ModuleCat.restrictScalars ψ).map z₀) ≫
        affineTildePushforwardCohomologyMap D B ψ Cg i := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  let : (affinePushforwardTilde D).Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of D) f g
  let P := Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))
  let : P.Additive := inferInstance
  let : (affinePushforwardTilde D ⋙ P).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by
      rw [Functor.comp_map, (affinePushforwardTilde D).map_zero]
      exact P.map_zero _ _⟩
  let N := ((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj M
  let N' := ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℤ)).obj N
  have e := exactDerivedHomology T N' i _ _ (m.cohomologyIso i).hom
    (m.counit.app ((HomotopyCategory.quotient _ _).obj N))
  let α := algebraMap (A ⊗[R] B) D
  let j : B →+* A ⊗[R] B := Algebra.TensorProduct.includeRight.toRingHom
  let E := ((ModuleCat.extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
    (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars (α.comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
    (.up ℤ)).obj M
  let Cg := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let ρ := ModuleCat.restrictScalarsComp' j α ψ hψ.symm
  let z : C ⟶ Cg := eqToHom (by dsimp only [C, Cg, α]; rw [hφ])
  have hk := coefficientHomology (ModuleCat.restrictScalars α)
    (ModuleCat.restrictScalars j) (ModuleCat.restrictScalars ψ) ρ.symm
    E C Cg m.ordinaryToLocalized z i
  have hm := m.comparison_eq i
  rw [homologyFactorsh_assoc N' i] at hm
  dsimp only
  have hsrc : (affineTildeDerivedTensorSourceIso R A B D M m i).hom =
      T.map (m.cohomologyIso i).hom ≫
        (T.mapDerivedCategoryHomologyFunctorIso i).hom.app
          (m.derived.obj (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient _ _).obj N))) := by rfl
  have hraw : affineTildeDerivedTensorToPushforward R A B D M m φ ψ hφ hψ =
      T.mapDerivedCategory.map (m.counit.app
        ((HomotopyCategory.quotient _ _).obj N)) ≫
      T.mapDerivedCategoryFactors.hom.app N' ≫
      affineTildeTensorOrdinaryTargetMap R A B D M φ ψ
        (affineTildeTensorCoefficientComplexMap R A B D M m φ ψ hφ hψ) := by
    change (𝟙 _ ≫ T.mapDerivedCategory.map (m.counit.app
      ((HomotopyCategory.quotient _ _).obj N)) ≫
        T.mapDerivedCategoryFactors.hom.app N') ≫ _ = _
    simp only [Category.id_comp, Category.assoc]
  rw [hsrc, hraw]
  unfold affineTildeTensorOrdinaryTargetMap
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% e]
  erw [exactComplexHomology_assoc T N' i]
  unfold affineTildeTensorCoefficientComplexMap
  simp only [HomologicalComplex.homologyMap_comp, Category.assoc]
  erw [← reassoc_of% hm]
  erw [hk]
  exact affineTildeCoefficientPushforwardHomologyCoordinates R A B D M m φ ψ hφ hψ i

end AlgebraicGeometry
