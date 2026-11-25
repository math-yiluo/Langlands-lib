/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

/-!
# Derived pro-etale direct image and restriction of scalars

## References

* Stacks Tags 03DA and 015F
* Stacks Tags 0D6E, 0D6J, 015F
-/

@[expose] public section

set_option autoImplicit false

universe u uC uD vC vD wC wD

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Restriction along the induced map of constant ring sheaves, using Mathlib's
unchanged-underlying-abelian-sheaf restriction functor. Its exactness is the instance
`proEtaleRingRestrictScalars_preservesFiniteLimits/Colimits`; its derived functor is
therefore the termwise `mapDerivedCategory`. -/
noncomputable abbrev proEtaleCoefficientRestrictScalars (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleRingModules X (proEtaleConstantRing X B) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) :=
  proEtaleRingRestrictScalars
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))

/-- Exact restriction preserves finite limits. -/
noncomputable instance proEtaleCoefficientRestrictScalars_preservesFiniteLimits
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (proEtaleCoefficientRestrictScalars X φ) :=
  (proEtaleRingRestrictScalars_properties
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))).1

/-- Exact restriction preserves finite colimits. -/
noncomputable instance proEtaleCoefficientRestrictScalars_preservesFiniteColimits
    (X : Scheme.{u}) {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteColimits (proEtaleCoefficientRestrictScalars X φ) :=
  (proEtaleRingRestrictScalars_properties
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))).2.1

private theorem coefficientDirectImage_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ.ulift.{u + 1, u + 1}) ≫ proEtaleCoefficientDirectImageMap f B =
      proEtaleCoefficientDirectImageMap f A ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})) := by
  apply ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A))) _).injective
  change ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _)
    ((presheafToSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
      ((Functor.const Y.ProEtᵒᵖ).map (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [proEtaleCoefficientDirectImageMap, proEtaleConstantDirectImageMap,
    Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext W
  exact congrArg (fun t ↦ t.app ((proEtaleBaseChange f).op.obj W))
    ((toSheafification (ProEt.topology X) CommRingCat.{u + 1}).naturality
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})))

private theorem coefficientInverseImage_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    (proEtaleConstantRingComparison f A).hom ≫
        (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom φ.ulift.{u + 1, u + 1}) =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom φ.ulift.{u + 1, u + 1})) ≫
        (proEtaleConstantRingComparison f B).hom := by
  symm
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map _ ≫
      (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  exact coefficientDirectImage_naturality f φ

private theorem coefficientRingDirectImage_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
        (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A) =
      proEtaleCoefficientDirectImageMap f A := by
  change (proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm
      (proEtaleCoefficientDirectImageMap f A)) = _
  exact Equiv.apply_symm_apply _ _

-- Generalize the structure maps before substituting their adjunction equalities.
-- This keeps sectionwise morphism coercions dependent on the maps throughout transport.
private noncomputable abbrev coefficientPushforwardWithMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (ρ : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) :
    proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      proEtaleRingModules Y (proEtaleConstantRing Y A) :=
  SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight ρ.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private instance coefficientPushforwardWithMap_additive
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (ρ : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) :
    (coefficientPushforwardWithMap f A ρ).Additive where
  map_add := by
    intro M N a b
    ext W n
    rfl

private theorem coefficientComparisonForMaps_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (ρA : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    (ρB : proEtaleConstantRing Y B ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X B))
    (hA : ρA = proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A))
    (hB : ρB = proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
      (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)) :
    ∃! e : coefficientPushforwardWithMap f B ρB ⋙ proEtaleCoefficientRestrictScalars Y φ ≅
        proEtaleCoefficientRestrictScalars X φ ⋙ coefficientPushforwardWithMap f A ρA,
      ∀ (N : proEtaleRingModules X (proEtaleConstantRing X B)) (W : Y.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  subst ρA
  subst ρB
  exact proEtaleRingRestrictionDirectImage_existsUnique f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ.ulift))
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ.ulift))
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (coefficientInverseImage_naturality f φ)

/-- The underived coefficient square has the uniquely normalized identity-on-sections
comparison. -/
theorem proEtaleCoefficientDirectImageComparison_existsUnique
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃! e : proEtaleConstantModuleDirectImage f B ⋙ proEtaleCoefficientRestrictScalars Y φ ≅
        proEtaleCoefficientRestrictScalars X φ ⋙ proEtaleConstantModuleDirectImage f A,
      ∀ (N : proEtaleRingModules X (proEtaleConstantRing X B)) (W : Y.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  exact coefficientComparisonForMaps_existsUnique f φ
    (proEtaleCoefficientDirectImageMap f A) (proEtaleCoefficientDirectImageMap f B)
    (coefficientRingDirectImage_eq f A).symm (coefficientRingDirectImage_eq f B).symm

/-- The actual identity-on-sections comparison, selected by its unique characterization. -/
noncomputable def proEtaleCoefficientDirectImageComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    proEtaleConstantModuleDirectImage f B ⋙ proEtaleCoefficientRestrictScalars Y φ ≅
      proEtaleCoefficientRestrictScalars X φ ⋙ proEtaleConstantModuleDirectImage f A :=
  Classical.choose (proEtaleCoefficientDirectImageComparison_existsUnique f φ)

private noncomputable def coefficientDerivedUnit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app K)

private theorem coefficientDerivedUnit_eq_inv
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) [K.IsKInjective] :
    coefficientDerivedUnit F K = (F.rightDerivedFunctorObjQIso K).inv := by
  simp only [coefficientDerivedUnit, Functor.rightDerivedFunctorObjQIso,
    Iso.trans_inv, Iso.symm_inv, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    asIso_hom, Category.assoc]

private theorem coefficientDerivedUnit_eq_homotopyUnit
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    coefficientDerivedUnit F K =
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) := by
  change 𝟙 _ ≫ F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
      F.rightDerivedFunctor.map (𝟙 (DerivedCategory.Q.obj K)) = _
  erw [F.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]

private theorem coefficientDerivedUnit_naturality
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ} (j : K ⟶ L) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
        coefficientDerivedUnit F L =
      coefficientDerivedUnit F K ≫ F.rightDerivedFunctor.map (DerivedCategory.Q.map j) := by
  have h := F.rightDerivedFunctorUnit.naturality ((HomotopyCategory.quotient _ _).map j)
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map j) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj L) =
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map j) at h
  simpa only [coefficientDerivedUnit_eq_homotopyUnit] using h

private noncomputable abbrev coefficientLocalization (X : Scheme.{u})
    (A : Type u) [CommRing A] :
    CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ ⥤
      proEtaleDerivedCategory X A :=
  @DerivedCategory.Q.{u + 2, u + 1, u + 2}
    (proEtaleRingModules X (proEtaleConstantRing X A)) _ _ (HasDerivedCategory.standard _)

private noncomputable abbrev coefficientDerivedRestriction (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A :=
  @Functor.mapDerivedCategory
    (proEtaleRingModules X (proEtaleConstantRing X B)) _ _ (HasDerivedCategory.standard _)
    (proEtaleRingModules X (proEtaleConstantRing X A)) _ _ (HasDerivedCategory.standard _)
    (proEtaleCoefficientRestrictScalars X φ) _ _ _

private noncomputable abbrev coefficientRestrictionFactors (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) :
    coefficientLocalization X B ⋙ coefficientDerivedRestriction X φ ≅
      (proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ) ⋙
        coefficientLocalization X A :=
  @Functor.mapDerivedCategoryFactors
    (proEtaleRingModules X (proEtaleConstantRing X B)) _ _ (HasDerivedCategory.standard _)
    (proEtaleRingModules X (proEtaleConstantRing X A)) _ _ (HasDerivedCategory.standard _)
    (proEtaleCoefficientRestrictScalars X φ) _ _ _

private noncomputable abbrev coefficientDerivedPushforwardWithMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (ρ : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A)) :
    proEtaleDerivedCategory X A ⥤ proEtaleDerivedCategory Y A :=
  @Functor.rightDerivedFunctor.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (proEtaleRingModules X (proEtaleConstantRing X A))
    (proEtaleRingModules Y (proEtaleConstantRing Y A))
    _ _ _ _ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (coefficientPushforwardWithMap f A ρ) _ _

private noncomputable abbrev coefficientUnitWithMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Type u) [CommRing A]
    (ρ : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    (K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ) :
    (coefficientLocalization Y A).obj
        (((coefficientPushforwardWithMap f A ρ).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (coefficientDerivedPushforwardWithMap f A ρ).obj ((coefficientLocalization X A).obj K) :=
  @coefficientDerivedUnit.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
    (proEtaleRingModules X (proEtaleConstantRing X A))
    (proEtaleRingModules Y (proEtaleConstantRing Y A))
    _ _ _ _ (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _
    (coefficientPushforwardWithMap f A ρ) _ K

private theorem coefficientDerivedComparisonForMaps_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (ρA : proEtaleConstantRing Y A ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X A))
    (ρB : proEtaleConstantRing Y B ⟶
      (proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj (proEtaleConstantRing X B))
    (hA : ρA = proEtaleRingDirectImageMap f (proEtaleConstantRing Y A)
      (proEtaleConstantRing X A) (proEtaleConstantRingComparison f A))
    (hB : ρB = proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
      (proEtaleConstantRing X B) (proEtaleConstantRingComparison f B)) :
    ∃ d : coefficientDerivedPushforwardWithMap f B ρB ⋙
        (coefficientDerivedRestriction Y φ) ≅
      (coefficientDerivedRestriction X φ) ⋙
        coefficientDerivedPushforwardWithMap f A ρA,
      ∀ K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ,
        (coefficientDerivedRestriction Y φ).map
            (coefficientUnitWithMap f B ρB K) ≫
          d.hom.app ((coefficientLocalization X B).obj K) ≫
          (coefficientDerivedPushforwardWithMap f A ρA).map
            ((coefficientRestrictionFactors X φ).hom.app K) =
        (coefficientRestrictionFactors Y φ).hom.app
            (((coefficientPushforwardWithMap f B ρB).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (coefficientLocalization Y A).map
            ((NatIso.mapHomologicalComplex (Classical.choose
                (coefficientComparisonForMaps_existsUnique f φ ρA ρB hA hB))
              (.up ℤ)).hom.app K) ≫
          coefficientUnitWithMap f A ρA
            (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  subst ρA
  subst ρB
  exact proEtaleRingRestrictionDerivedDirectImage_exists f
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B)
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ.ulift))
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom φ.ulift))
    (proEtaleConstantRingComparison f A) (proEtaleConstantRingComparison f B)
    (coefficientInverseImage_naturality f φ)

private theorem coefficientDerivedComparison_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃ d : proEtaleConstantDerivedDirectImage f B ⋙
        (coefficientDerivedRestriction Y φ) ≅
      (coefficientDerivedRestriction X φ) ⋙
        proEtaleConstantDerivedDirectImage f A,
      ∀ K : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ,
        (coefficientDerivedRestriction Y φ).map
            (coefficientUnitWithMap f B (proEtaleCoefficientDirectImageMap f B) K) ≫
          d.hom.app ((coefficientLocalization X B).obj K) ≫
          (proEtaleConstantDerivedDirectImage f A).map
            ((coefficientRestrictionFactors X φ).hom.app K) =
        (coefficientRestrictionFactors Y φ).hom.app
            (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj K) ≫
          (coefficientLocalization Y A).map
            ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
              (.up ℤ)).hom.app K) ≫
          coefficientUnitWithMap f A (proEtaleCoefficientDirectImageMap f A)
            (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact coefficientDerivedComparisonForMaps_exists f φ
    (proEtaleCoefficientDirectImageMap f A) (proEtaleCoefficientDirectImageMap f B)
    (coefficientRingDirectImage_eq f A).symm (coefficientRingDirectImage_eq f B).symm

/-- Derived direct image commutes with restriction of finite commutative coefficients.
The displayed equality says that the comparison is the inverse of f_*(j), after the
canonical termwise-localization and K-injective resolution identifications. In particular
restriction of scalars is not assumed to preserve K-injectivity. -/
theorem proEtaleDerivedDirectImage_restrictScalars
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∃ d : (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory ⋙
        proEtaleConstantDerivedDirectImage f A ≅
      proEtaleConstantDerivedDirectImage f B ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory,
      ∀ (J : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X B)) ℤ)
        [J.IsKInjective]
        (I : CochainComplex (proEtaleRingModules X (proEtaleConstantRing X A)) ℤ)
        [I.IsKInjective]
        (j : ((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J ⟶ I)
        [QuasiIso j],
        QuasiIso (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j) ∧
        d.hom.app (DerivedCategory.Q.obj J) ≫
            (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
              ((proEtaleConstantModuleDirectImage f B).rightDerivedFunctorObjQIso J).hom ≫
            (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors.hom.app
              (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj J) ≫
            DerivedCategory.Q.map
              ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
                (.up ℤ)).hom.app J) ≫
            DerivedCategory.Q.map
              (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j) =
          (proEtaleConstantDerivedDirectImage f A).map
              ((proEtaleCoefficientRestrictScalars X φ).mapDerivedCategoryFactors.hom.app J) ≫
            (proEtaleConstantDerivedDirectImage f A).map (DerivedCategory.Q.map j) ≫
            ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso I).hom := by
  obtain ⟨d, hd⟩ := coefficientDerivedComparison_exists f φ
  refine ⟨d.symm, ?_⟩
  intro J hJ I hI j hj
  have hu := hd J
  dsimp only [coefficientUnitWithMap] at hu
  rw [coefficientDerivedUnit_eq_inv _ J] at hu
  change (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
      ((proEtaleConstantModuleDirectImage f B).rightDerivedFunctorObjQIso J).inv ≫
      d.hom.app (DerivedCategory.Q.obj J) ≫
      (proEtaleConstantDerivedDirectImage f A).map
        ((proEtaleCoefficientRestrictScalars X φ).mapDerivedCategoryFactors.hom.app J) =
    (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors.hom.app
        (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj J) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
          (.up ℤ)).hom.app J) ≫
      coefficientDerivedUnit (proEtaleConstantModuleDirectImage f A)
        (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J) at hu
  have hunit : IsIso
      (coefficientDerivedUnit.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
              (proEtaleConstantModuleDirectImage f A)
        (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J)) := by
    have hh : IsIso
        ((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors.hom.app
            (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj J) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
              (.up ℤ)).hom.app J) ≫
          coefficientDerivedUnit.{u + 2, u + 2, u + 1, u + 1, u + 2, u + 2}
            (proEtaleConstantModuleDirectImage f A)
            (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J)) := by
      rw [← hu]
      infer_instance
    have hh' := IsIso.of_isIso_comp_left
      ((proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors.hom.app
        (((proEtaleConstantModuleDirectImage f B).mapHomologicalComplex (.up ℤ)).obj J))
      (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
            (.up ℤ)).hom.app J) ≫
        coefficientDerivedUnit (proEtaleConstantModuleDirectImage f A)
          (((proEtaleCoefficientRestrictScalars X φ).mapHomologicalComplex (.up ℤ)).obj J))
    exact IsIso.of_isIso_comp_left
      (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (proEtaleCoefficientDirectImageComparison f φ)
          (.up ℤ)).hom.app J)) _
  have hn := coefficientDerivedUnit_naturality (proEtaleConstantModuleDirectImage f A) j
  rw [coefficientDerivedUnit_eq_inv _ I] at hn
  have hmap : IsIso (DerivedCategory.Q.map
      (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j)) := by
    have hh : IsIso (DerivedCategory.Q.map
        (((proEtaleConstantModuleDirectImage f A).mapHomologicalComplex (.up ℤ)).map j) ≫
          ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso I).inv) := by
      rw [hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso I).inv
  refine ⟨(DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hmap, ?_⟩
  apply (cancel_mono
    ((proEtaleConstantModuleDirectImage f A).rightDerivedFunctorObjQIso I).inv).1
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hn]
  have hh := congrArg (fun t ↦
    d.inv.app (DerivedCategory.Q.obj J) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((proEtaleConstantModuleDirectImage f B).rightDerivedFunctorObjQIso J).hom ≫ t ≫
      (proEtaleConstantDerivedDirectImage f A).map (DerivedCategory.Q.map j)) hu
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id] at hh
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc] at hh
  exact hh.symm

end AlgebraicGeometry.Scheme
