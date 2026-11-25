/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
import WeilConjectures.AlgebraicGeometry.TensorPullbackTilde
import WeilConjectures.AlgebraicGeometry.AffineTildeTotalTensor
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorComparisonDescent
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Affine computations of derived pullback and tensor

Source: Stacks Project, Lemmas 36.3.8(2), 36.3.9(2), Tags 08DW and 08DX,
and Lemma 36.3.6, Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).

The affine formulas are written for every K-flat resolution `P ⟶ M`.
Thus the right sides are the concrete representatives of the module derived tensors,
with no boundedness, flatness of the ring map, or quasi-coherence hypothesis added.

## Main statements

- `derivedPullback_openRestriction_iso`: restriction of derived pullback.
- `derivedTensor_openRestriction_iso`: restriction of derived tensor, natural in both factors.
- `derivedPullback_tilde_iso`: affine pullback on any K-flat resolution.
- `derivedTensor_tilde_iso`: affine tensor on any K-flat resolution of the first factor.
- `derivedPullback_tilde_kFlat_natIso`: natural affine pullback comparison on K-flat models.
- `derivedTensor_tilde_kFlat_natIso`: natural affine tensor comparison on K-flat models.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry


attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private instance tilde_additive (A : Type u) [CommRing A] :
    (tilde.functor (.of A) : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)).Additive :=
  ⟨by intros; exact tilde.map_add _ _⟩

private theorem tensorDerivedCounit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∃ (_ : (Scheme.Modules.tensorPullback f).Additive)
      (ε : DerivedCategory.Qh.{w} ⋙ derivedPullback f ⟶
        (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh.{w}
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))),
      (derivedPullback f).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) ∧
      ∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P →
          IsIso (ε.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by
  have d := derivedPullback_spec f
  obtain ⟨E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
    d.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  exact ⟨hEadd, ε, hL, hK⟩

private theorem pullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    Nonempty (derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g)) := by
  obtain ⟨ag, εg, hLg, hKg⟩ := tensorDerivedCounit g
  obtain ⟨af, εf, hLf, hKf⟩ := tensorDerivedCounit f
  obtain ⟨ac, εc, hLc, hKc⟩ := tensorDerivedCounit (f ≫ g)
  let := hLc
  obtain ⟨θ⟩ := Scheme.Modules.nonempty_tensorPullbackComp f g
  let β : DerivedCategory.Qh.{w} ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      (Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory (.up ℤ) ⋙
        (DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
    (Functor.associator DerivedCategory.Qh.{w} (derivedPullback g)
      (derivedPullback f)).inv ≫
    Functor.whiskerRight εg (derivedPullback f) ≫
    (Functor.associator _ DerivedCategory.Qh.{w} (derivedPullback f)).hom ≫
    Functor.whiskerLeft _ εf ≫
    (Functor.associator _ _
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u}
        (moduleRings X.toRingedSpace)))).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso θ.symm (.up ℤ)).hom
      (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let τ := (derivedPullback (f ≫ g)).leftDerivedLift εc
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
    (derivedPullback g ⋙ derivedPullback f) β
  have hflat (P : CochainComplex
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
      (hP : CochainComplex.IsKFlatTensor (R := Z.sheaf) P) :
      IsIso (τ.app (DerivedCategory.Qh.{w}.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
    have hg := hKg P hP
    have hfg := hKc P hP
    have hPg : CochainComplex.IsKFlatTensor (R := Y.sheaf)
        (((Scheme.Modules.tensorPullback g).mapHomologicalComplex (.up ℤ)).obj P) := by
      exact CochainComplex.isKFlat_pullback g.base Y.sheaf Z.sheaf ⟨g.c⟩ P hP
    have hf := hKf _ hPg
    have hfapp : IsIso (εf.app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
      rw [Functor.mapHomotopyCategory_obj]
      exact hf
    have fac := (derivedPullback (f ≫ g)).leftDerived_fac_app εc
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ))
      (derivedPullback g ⋙ derivedPullback f) β
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
    have : IsIso (τ.app (DerivedCategory.Qh.{w}.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
          εc.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
      rw [show τ.app _ ≫ _ = _ from fac]
      dsimp only [β, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
      have h1 : IsIso ((derivedPullback f).map
          (εg.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := inferInstance
      have h2 : IsIso ((DerivedCategory.Qh.{w}
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
          ((Functor.mapHomotopyCategoryCompIso θ.symm (.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := inferInstance
      simp only [Category.id_comp]
      exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' hfapp h2)
    exact IsIso.of_isIso_comp_right _ (εc.app _)
  have : IsIso τ := by
    apply (NatTrans.isIso_iff_isIso_app τ).2
    intro K
    let Q := DerivedCategory.Qh.{w}
      (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    apply (NatTrans.isIso_app_iff_of_iso τ (Q.objObjPreimageIso K)).1
    obtain ⟨G, hG⟩ := HomotopyCategory.quotient_obj_surjective (Q.objPreimage K)
    rw [← hG]
    obtain ⟨P, s, hP, _, hs, _⟩ :=
      CochainComplex.exists_isKFlatResolution (R := Z.sheaf) G
    have hsq := (HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs
    have := Localization.inverts Q (HomotopyCategory.quasiIso _ (.up ℤ)) _ hsq
    apply (NatTrans.isIso_app_iff_of_iso τ
      (asIso (Q.map ((HomotopyCategory.quotient _ (.up ℤ)).map s)))).1
    exact hflat P hP
  exact ⟨asIso τ⟩

private theorem pullbackOpenIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))] :
    let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      (Scheme.Modules.overEquiv U).functor
    Nonempty (derivedPullback U.ι ≅ Functor.mapDerivedCategory.{w, w} R) := by
  dsimp only
  let R : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
    (Scheme.Modules.overEquiv U).functor
  obtain ⟨a, ε, hL, _⟩ := tensorDerivedCounit U.ι
  let := hL
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction U.ι
  let θ : Scheme.Modules.tensorPullback U.ι ≅ R :=
    adj.leftAdjointUniq (Scheme.Modules.restrictAdjunction U.ι) ≪≫
      (Scheme.Modules.overFunctorEquiv U).symm
  have : R.Additive := by dsimp [R]; infer_instance
  have : PreservesFiniteLimits R := by dsimp [R]; infer_instance
  have : PreservesFiniteColimits R := by dsimp [R]; infer_instance
  let θh : (Scheme.Modules.tensorPullback U.ι).mapHomotopyCategory (.up ℤ) ≅
      R.mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.hom_inv_id]; rfl
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.inv_hom_id]; rfl }
  let δ := Functor.isoWhiskerRight θh
    (DerivedCategory.Qh.{w} (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)))
  let α := (Functor.mapDerivedCategoryFactorsh.{w, w} R) ≪≫ δ.symm
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
    (Functor.mapDerivedCategory.{w, w} R) α
  exact ⟨Functor.leftDerivedUnique (Functor.mapDerivedCategory.{w, w} R) (derivedPullback U.ι)
    ε α.hom (HomotopyCategory.quasiIso _ (.up ℤ))⟩

/-- Derived pullback commutes naturally with restriction to opens.
Source: Stacks, Tag 08DW, proof
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution on Y (lem-pc-kflat-resolution).
Restriction to V preserves K-flatness (lem-pc-kflat-pullback-preservation).
Termwise tensor pullback and restriction commute, so both composite functors are
computed by the same pulled-back restricted resolution
(lemma-coherent-base-change-invertible-sheaves--2). The resolution comparison is natural and
descends to the derived category. -/
theorem derivedPullback_openRestriction_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : X.Opens) (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))] :
    Nonempty (derivedPullback f ⋙
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
      (SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) V ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))
          (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
          (Scheme.Modules.overEquiv V)).mapDerivedCategory ⋙
        derivedPullback (f.resLE V U hUV)) := by
  obtain ⟨a⟩ := pullbackOpenIso X U
  obtain ⟨b⟩ := pullbackOpenIso Y V
  obtain ⟨c⟩ := pullbackCompIso U.ι f
  obtain ⟨d⟩ := pullbackCompIso (f.resLE V U hUV) V.ι
  refine ⟨Functor.isoWhiskerLeft (derivedPullback f) a.symm ≪≫ c ≪≫ ?_ ≪≫
    d.symm ≪≫ Functor.isoWhiskerRight b (derivedPullback (f.resLE V U hUV))⟩
  exact eqToIso (congrArg (fun k ↦ derivedPullback k) (Scheme.Hom.resLE_comp_ι f hUV).symm)

/-- Derived tensor commutes with restriction to any open subscheme.
Source: Stacks, Tag 08DX, proof; the restriction computation of Tag 08DW
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 1): choose a K-flat resolution of K (lem-pc-kflat-resolution).
It remains K-flat on U (lem-pc-kflat-pullback-preservation). Restriction commutes
with sheaf tensor and all direct sums in the signed total complex
(def-pc-tensor-complex-sheaves), so it identifies the two derived tensors.
The comparisons are induced by restriction of the total tensor complex. -/
theorem derivedTensor_openRestriction_iso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    : Nonempty
      (curriedTensor (schemeDerivedCategory X) ⋙
        (Functor.whiskeringRight (schemeDerivedCategory X) (schemeDerivedCategory X)
          (schemeDerivedCategory U.toScheme)).obj
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory ⋙
          curriedTensor (schemeDerivedCategory U.toScheme) ⋙
          (Functor.whiskeringLeft (schemeDerivedCategory X)
            (schemeDerivedCategory U.toScheme) (schemeDerivedCategory U.toScheme)).obj
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory) := by
  obtain ⟨F, hF, hmap, hadd, ε, hε, φ, _, hnat, hiso⟩ :=
    derivedPullback_tensorProduct U.ι
  obtain ⟨μ, _⟩ := derivedPullback_tensor_comparison_exists U.ι F hF hmap ε hε
    φ hnat hiso
  obtain ⟨a⟩ := pullbackOpenIso X U
  exact ⟨(curriedTensorPostFunctor.mapIso a).symm ≪≫ μ.symm ≪≫
    curriedTensorPreFunctor.mapIso a⟩

private theorem moduleKFlat_acyclic (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P)
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (hF : F.Acyclic) :
    (CochainComplex.mapBifunctor F P (curriedTensor (ModuleCat.{u} A))).Acyclic := by
  have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)).mp
      ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
  have hF' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
    (h _ hF').2

private theorem counitComparison
    {C D I : Type*} [Category C] [Category D] [Category I]
    [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (E₀ : C ⥤ D) [E₀.Additive]
    (L : DerivedCategory.{w} C ⥤ DerivedCategory.{w} D)
    (F : I ⥤ CochainComplex C ℤ)
    (ε : DerivedCategory.Qh.{w} ⋙ L ⟶
      E₀.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w})
    [IsIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε)] :
    Nonempty (F ⋙ DerivedCategory.Q.{w} ⋙ L ≅
      F ⋙ E₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w}) := by
  exact ⟨ Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft F (DerivedCategory.quotientCompQhIso _).symm) L ≪≫
    asIso (Functor.whiskerLeft (F ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft F
        (E₀.mapHomotopyCategoryFactors (.up ℤ)))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft (F ⋙ E₀.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso _)⟩

private theorem baseChangeCounitComparison
    {A₀ B₀ C D I : Type*}
    [Category A₀] [Category B₀] [Category C] [Category D] [Category I]
    [Preadditive A₀] [Preadditive B₀] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    (T : A₀ ⥤ C) (S : B₀ ⥤ D) (H : A₀ ⥤ B₀) (E : C ⥤ D)
    [T.Additive] [S.Additive] [H.Additive] [E.Additive]
    (L : DerivedCategory.{w} C ⥤ DerivedCategory.{w} D)
    (F : I ⥤ CochainComplex A₀ ℤ)
    (ε : DerivedCategory.Qh.{w} ⋙ L ⟶
      E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh.{w})
    (θ : T ⋙ E ≅ H ⋙ S)
    (hε : ∀ P, IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((T.mapHomologicalComplex (.up ℤ)).obj (F.obj P))))) :
    Nonempty (F ⋙ T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⋙ L ≅
      F ⋙ H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q.{w}) := by
  have : IsIso (Functor.whiskerLeft
      ((F ⋙ T.mapHomologicalComplex (.up ℤ)) ⋙ HomotopyCategory.quotient _ (.up ℤ)) ε) :=
    (NatTrans.isIso_iff_isIso_app _).2 hε
  obtain ⟨β⟩ := counitComparison E L (F ⋙ T.mapHomologicalComplex (.up ℤ)) ε
  let δ : T.mapHomologicalComplex (.up ℤ) ⋙ E.mapHomologicalComplex (.up ℤ) ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ S.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso θ (.up ℤ)
  exact ⟨β ≪≫ Functor.isoWhiskerLeft F
    (Functor.isoWhiskerRight δ DerivedCategory.Q.{w})⟩

/-- Naturality of the affine pullback comparison on K-flat module models.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): apply the natural termwise tilde/base-change isomorphism
(lem-weil-pbc-tilde-pullback-base-change) to K-flat complexes. Their tilde complexes
are K-flat (lem-pc-affine-tilde-kflat), so the derived-pullback counit is invertible
there (lemma-coherent-base-change-invertible-sheaves--2). Compose the two natural comparisons. For
arbitrary M use a K-flat resolution P to M; exact tilde sends it to an isomorphism after Q
(lem-pc-affine-qcoh-derived-equivalence). Naturality on K-flat models gives compatibility
with resolution comparisons, hence the affine formula independent of that choice. -/
theorem derivedPullback_tilde_kFlat_natIso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙
          DerivedCategory.Q ⋙ derivedPullback (Spec.map (CommRingCat.ofHom φ)) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ) ⋙
          (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} B ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
            (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨hEadd, ε, hε, hflat⟩ := tensorDerivedCounit f
  obtain ⟨θ, _⟩ := Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ)
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace) := tilde.functor (.of B)
  have : TA.Additive := tilde_additive A
  have : TB.Additive := tilde_additive B
  apply baseChangeCounitComparison TA TB
    (ModuleCat.extendScalars φ) (Scheme.Modules.tensorPullback f)
    (derivedPullback f) (CochainComplex.ιKFlat (ModuleCat.{u} A)) ε θ
  intro P
  apply hflat
  exact isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property)

/-- Naturality of the affine tensor comparison in a K-flat first model and an arbitrary
second complex. Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): tilde of the first model is K-flat (lem-pc-affine-tilde-kflat).
Compute sheaf derived tensor by that model (def-pc-kflat-complex). Apply the natural
tilde/tensor isomorphism in each bidegree (lem-weil-pbc-affine-tilde-tensor), then
preservation of arbitrary coproducts by tilde, to obtain the total-complex comparison
(def-pc-tensor-complex-sheaves). All maps commute with both differentials and with
maps in both variables. Resolve an arbitrary first complex (lem-pc-kflat-resolution);
exactness of tilde (lem-pc-affine-qcoh-derived-equivalence) and naturality give the
comparison for it, independently of the chosen resolution. -/
theorem derivedTensor_tilde_kFlat_natIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    Nonempty
      (CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
        (@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q ⋙
          curriedTensor (schemeDerivedCategory (Spec (.of A))) ⋙
          (Functor.whiskeringLeft (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q) ≅
        CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙
          (curriedTensor (ModuleCat.{u} A)).map₂CochainComplex ⋙
          (Functor.whiskeringRight (CochainComplex (ModuleCat.{u} A) ℤ)
            (CochainComplex (ModuleCat.{u} A) ℤ)
            (schemeDerivedCategory (Spec (.of A)))).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)) ⋙ DerivedCategory.Q)) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  let F := CochainComplex.ιKFlat (ModuleCat.{u} A) ⋙ T
  have hβ := kFlat_derivedTensor_comparison_natIso (Spec (.of A)) F T
    (fun P ↦ isKFlat_tilde A P.obj (moduleKFlat_acyclic A P.obj P.property))
  have hθ := affineTilde_totalTensor_natIso A
  refine Nonempty.map2 ?_ hβ hθ
  intro β θ
  let ι := CochainComplex.ιKFlat (ModuleCat.{u} A)
  exact (Functor.associator ι T _).symm ≪≫ β ≪≫
    Functor.associator ι T _ ≪≫ Functor.isoWhiskerLeft ι θ



private theorem affineTilde_Q_map_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (s : P ⟶ M) (hs : QuasiIso s) :
    IsIso (DerivedCategory.Q.map
      (((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ))).map s)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨e, ⟨α⟩, _⟩ := exists_affineQCohDerivedEquivalence A
  have : QuasiIso s := hs
  exact (NatIso.isIso_map_iff α s).mp (by
    change IsIso (((e.functor ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).map
      (DerivedCategory.Q.map s)))
    infer_instance)

private theorem mapIso_trans_nonempty
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P M : C} {N : D} (s : P ⟶ M) [IsIso s] (e : F.obj P ≅ N) :
    Nonempty (F.obj M ≅ N) :=
  ⟨F.mapIso (asIso s).symm ≪≫ e⟩

private theorem tensorIso_trans_nonempty
    {C : Type*} [Category C] [MonoidalCategory C]
    {P M N R : C} (s : P ⟶ M) [IsIso s] (e : P ⊗ N ≅ R) :
    Nonempty (M ⊗ N ≅ R) :=
  ⟨tensorIso (asIso s).symm (Iso.refl N) ≪≫ e⟩

/-- Affine derived pullback of termwise tilde is termwise tilde of derived base change,
computed on any K-flat resolution of the input complex.
Source: Stacks, Tag 08DW(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 2): resolve M by P (lem-pc-kflat-resolution). Termwise tilde
preserves quasi-isomorphisms (lem-pc-affine-qcoh-derived-equivalence), and tilde P
is K-flat (lem-pc-affine-tilde-kflat). Derived pullback is therefore represented
by termwise tensor pullback of tilde P (lemma-coherent-base-change-invertible-sheaves--2).
The natural tilde/base-change comparison in each degree
(lem-weil-pbc-tilde-pullback-base-change) identifies this with tilde of B tensor P.
This complex computes M tensor-derived B since P is K-flat. -/
theorem derivedPullback_tilde_iso (A B : Type u) [CommRing A] [CommRing B]
    (φ : A →+* B)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))]
    (M P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      ((derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} B ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace))
              (tilde.functor (.of B))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedPullback_tilde_kFlat_natIso A B φ
  exact mapIso_trans_nonempty (derivedPullback (Spec.map (CommRingCat.ofHom φ)))
    (DerivedCategory.Q.map (T.map s)) (α.app ⟨P, hP⟩)

/-- On an affine scheme, derived tensor of termwise tilde complexes is termwise tilde
of module derived tensor, computed with any K-flat resolution of the first factor.
Source: Stacks, Tag 08DX(2), via Tag 08DV
(blueprint: lem-pc-affine-derived-pullback-tensor-tilde).
Proof (node step 3): resolve M by P (lem-pc-kflat-resolution). Exactness of termwise
tilde (lem-pc-affine-qcoh-derived-equivalence) and K-flatness of tilde P
(lem-pc-affine-tilde-kflat) allow the sheaf derived tensor to be computed by
Tot(tilde P tensor tilde N) (def-pc-kflat-complex, def-pc-tensor-complex-sheaves).
In each bidegree apply lem-weil-pbc-affine-tilde-tensor; its naturality respects
both differentials. Tilde preserves the direct sums used in totalization, yielding
tilde Tot(P tensor N). This computes M tensor-derived N since P is K-flat.
The sum over p+q=n can be infinite for unbounded complexes; all coproducts, not just
finite ones, are preserved by tilde, which is a left adjoint. -/
theorem derivedTensor_tilde_iso (A : Type u) [CommRing A]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (M N P : CochainComplex (ModuleCat.{u} A) ℤ) (s : P ⟶ M) (hs : QuasiIso s)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat P) :
    Nonempty
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ⊗
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj N) ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
            (@id (ModuleCat.{u} A ⥤
              SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
              (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
                (CochainComplex.mapBifunctor P N (curriedTensor (ModuleCat.{u} A))))) := by
  let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
    (@id (ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
  have : IsIso (DerivedCategory.Q.map (T.map s)) := affineTilde_Q_map_isIso A s hs
  obtain ⟨α⟩ := derivedTensor_tilde_kFlat_natIso A
  exact tensorIso_trans_nonempty (DerivedCategory.Q.map (T.map s))
    ((α.app ⟨P, hP⟩).app N)


end AlgebraicGeometry
