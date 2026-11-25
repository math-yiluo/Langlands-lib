/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Augmentation compatibility through computing reduction counits

The exact-square factor identity and normalized unit equations imply compatibility
of the derived comparison with augmentation, first on resolving complexes and then
on the derived category. These proved helpers support the stratum restriction proof.
Source: Stacks Tags 03EL, 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local instance] completedReductionModuleTowerFunctor_additive
attribute [local irreducible] HasDerivedCategory.standard
  cochainRepresentativeWhiskering complexCounitNat
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
  completedReductionTower CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors CategoryTheory.Functor.mapDerivedCategoryFactorsh
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local irreducible] completedReductionModuleTowerFunctor
  completedReductionTowerComplexCounit reductionComplexCounit coherenceReductionTowerCounit

/-- Ordinary augmentation compatibility descends through computing reduction counits.
Source: Stacks Tags 03EL, 06YY
(blueprint: lem-weil-pbc-derived-reduction-augmentation-of-counits).
Proof: on resolving complexes, postcompose with the invertible target counit and
apply the representative comparison equation. The two unit normalizations reduce
the equation to the ordinary augmented square and the exact derived localization
factors. Fully faithful restriction to resolving complexes gives the equation for
every derived object. -/
theorem derivedReduction_augmentationOfCounits
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : B ⥤ C) (G : D ⥤ E) (RX CX : B ⥤ D) (RY CY : C ⥤ E)
    [F.Additive] [G.Additive] [RX.Additive] [RY.Additive]
    [CX.Additive] [CY.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits CX] [PreservesFiniteColimits CX]
    [PreservesFiniteLimits CY] [PreservesFiniteColimits CY]
    (LX : DerivedCategory B ⥤ DerivedCategory D)
    (LY : DerivedCategory C ⥤ DerivedCategory E)
    (cX : ∀ P : CochainComplex B ℤ, LX.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RX.mapHomologicalComplex (.up ℤ)).obj P))
    (cY : ∀ P : CochainComplex C ℤ, LY.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P))
    (uX : CX ⟶ RX) (uY : CY ⟶ RY)
    (iX : CX.mapDerivedCategory ⟶ LX) (iY : CY.mapDerivedCategory ⟶ LY)
    (e : RX ⋙ G ≅ F ⋙ RY) (c : CX ⋙ G ≅ F ⋙ CY)
    (τ : LX ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ LY)
    (good : ObjectProperty (CochainComplex B ℤ))
    (res : ∀ K, ∃ (P : CochainComplex B ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hiso : ∀ P, good P → IsIso (cY ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (hnorm : ∀ P, good P →
      DerivedReductionComparisonFormula F G RX RY LX LY cX cY e τ P)
    (hX : ∀ P, good P → iX.app (DerivedCategory.Q.obj P) ≫ cX P =
      CX.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex uX (.up ℤ)).app P))
    (hY : ∀ P, good P →
      iY.app (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        cY ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      CY.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex uY (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)))
    (hOrd : ∀ M, G.map (uX.app M) ≫ e.hom.app M = c.hom.app M ≫ uY.app (F.obj M)) :
    ∀ K : DerivedCategory B,
      G.mapDerivedCategory.map (iX.app K) ≫ τ.hom.app K =
        (Functor.mapDerivedCategoryCompIso CX G ≪≫
          Functor.mapDerivedCategoryNatIso c ≪≫
            (Functor.mapDerivedCategoryCompIso F CY).symm).hom.app K ≫
          iY.app (F.mapDerivedCategory.obj K) := by
  have heq :
    Functor.whiskerRight iX G.mapDerivedCategory ≫ τ.hom =
      (Functor.mapDerivedCategoryCompIso CX G ≪≫
        Functor.mapDerivedCategoryNatIso c ≪≫
          (Functor.mapDerivedCategoryCompIso F CY).symm).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory iY := by
    let ff := cochainRepresentativeWhiskering good res (DerivedCategory E)
    apply ff.map_injective
    ext Y
    let P := Y.obj
    have hP : good P := Y.property
    let Fc := F.mapHomologicalComplex (.up ℤ)
    let FT := G.mapDerivedCategory
    let Ftc := G.mapHomologicalComplex (.up ℤ)
    let ay := (NatTrans.mapHomologicalComplex uX (.up ℤ)).app P
    let ax := (NatTrans.mapHomologicalComplex uY (.up ℤ)).app (Fc.obj P)
    let oc := (NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P
    let cc := (NatIso.mapHomologicalComplex c (.up ℤ)).hom.app P
    let s := F.mapDerivedCategoryFactors.hom.app P
    let cx := cY (Fc.obj P)
    have : IsIso cx := hiso P hP
    have : IsIso (LY.map s ≫ cx) := by dsimp [s]; infer_instance
    have hN := hnorm P hP
    change τ.hom.app (DerivedCategory.Q.obj P) ≫ LY.map s ≫ cx =
      FT.map (cX P) ≫ G.mapDerivedCategoryFactors.hom.app
        ((RX.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map oc at hN
    have hOrd' : Ftc.map ay ≫ oc = cc ≫ ax := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact hOrd (P.X i)
    change FT.map (iX.app (DerivedCategory.Q.obj P)) ≫ τ.hom.app _ = _
    apply (cancel_mono (LY.map s ≫ cx)).1
    calc
      _ = FT.map (iX.app (DerivedCategory.Q.obj P)) ≫
          (FT.map (cX P) ≫ G.mapDerivedCategoryFactors.hom.app
            ((RX.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map oc) := by
        simpa only [Category.assoc] using
          congrArg (fun z ↦ FT.map (iX.app (DerivedCategory.Q.obj P)) ≫ z) hN
      _ = FT.map (iX.app (DerivedCategory.Q.obj P) ≫ cX P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((RX.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map oc := by
        rw [FT.map_comp]
        simp only [Category.assoc]
      _ = FT.map (CX.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map ay) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((RX.mapHomologicalComplex (.up ℤ)).obj P) ≫ DerivedCategory.Q.map oc := by
        rw [hX P hP]
      _ = FT.map (CX.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((CX.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (Ftc.map ay ≫ oc) := by
        rw [FT.map_comp]
        simp only [Category.assoc]
        erw [G.mapDerivedCategoryFactors.hom.naturality_assoc ay]
        rw [DerivedCategory.Q.map_comp]
        rfl
      _ = FT.map (CX.mapDerivedCategoryFactors.hom.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((CX.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (cc ≫ ax) := by rw [hOrd']
      _ = (Functor.mapDerivedCategoryCompIso CX G ≪≫
            Functor.mapDerivedCategoryNatIso c ≪≫
              (Functor.mapDerivedCategoryCompIso F CY).symm).hom.app (DerivedCategory.Q.obj P) ≫
          CY.mapDerivedCategory.map s ≫ CY.mapDerivedCategoryFactors.hom.app (Fc.obj P) ≫
            DerivedCategory.Q.map ax := by
        simpa only [FT, Fc, s, cc, NatIso.mapHomologicalComplex,
          Functor.mapDerivedCategorySquareIso, Category.assoc, DerivedCategory.Q.map_comp] using
          congrArg (fun z ↦ z ≫ DerivedCategory.Q.map ax)
            (Functor.exactSquare_fac c P).symm
      _ = (Functor.mapDerivedCategoryCompIso CX G ≪≫
            Functor.mapDerivedCategoryNatIso c ≪≫
              (Functor.mapDerivedCategoryCompIso F CY).symm).hom.app (DerivedCategory.Q.obj P) ≫
          CY.mapDerivedCategory.map s ≫ iY.app (DerivedCategory.Q.obj (Fc.obj P)) ≫ cx := by
        simpa only [Category.assoc] using congrArg (fun z ↦
          (Functor.mapDerivedCategoryCompIso CX G ≪≫
            Functor.mapDerivedCategoryNatIso c ≪≫
              (Functor.mapDerivedCategoryCompIso F CY).symm).hom.app (DerivedCategory.Q.obj P) ≫
                CY.mapDerivedCategory.map s ≫ z) (hY P hP).symm
      _ = _ := by
        erw [← Category.assoc (CY.mapDerivedCategory.map s), iY.naturality s]
        simp only [Functor.whiskeringLeft, Functor.whiskerLeft_app,
          NatTrans.comp_app, Category.assoc]
        rfl
  intro K
  exact NatTrans.congr_app heq K

private theorem unitCounit_onComplex
    {B D : Type*} [Category B] [Category D] [Abelian B] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory D]
    (C R : B ⥤ D) [C.Additive] [R.Additive]
    [PreservesFiniteLimits C] [PreservesFiniteColimits C]
    (L : DerivedCategory B ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ R.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (i : C.mapDerivedCategory ⟶ L) (u : C ⟶ R) (P : CochainComplex B ℤ)
    (h : i.app (DerivedCategory.Q.obj P) ≫
        cast (by rfl) (ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)) =
      C.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P)) :
    i.app (DerivedCategory.Q.obj P) ≫ reductionComplexCounit R L ε P =
      C.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex u (.up ℤ)).app P) := by
  unfold reductionComplexCounit
  change i.app (DerivedCategory.Q.obj P) ≫
    (L.map (𝟙 _) ≫ ε.app ((HomotopyCategory.quotient B (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _) = _
  erw [L.map_id, DerivedCategory.Qh.map_id, Category.id_comp,
    Category.comp_id, Category.comp_id]
  exact h

private theorem exactSquare_fac
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : B ⥤ C) (G : D ⥤ E) (CX : B ⥤ D) (CY : C ⥤ E)
    [F.Additive] [G.Additive] [CX.Additive] [CY.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits CX] [PreservesFiniteColimits CX]
    [PreservesFiniteLimits CY] [PreservesFiniteColimits CY]
    (e : CX ⋙ G ≅ F ⋙ CY) (P : CochainComplex B ℤ) :
    (Functor.mapDerivedCategoryCompIso CX G ≪≫
        Functor.mapDerivedCategoryNatIso e ≪≫
          (Functor.mapDerivedCategoryCompIso F CY).symm).hom.app (DerivedCategory.Q.obj P) ≫
        CY.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        CY.mapDerivedCategoryFactors.hom.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (CX.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((CX.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  let : PreservesFiniteLimits (CX ⋙ G) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (CX ⋙ G) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (F ⋙ CY) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (F ⋙ CY) := comp_preservesFiniteColimits _ _
  have h1 := Functor.mapDerivedCategoryCompIso_fac F CY P
  have hc1 : (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ CY))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  erw [hc1, DerivedCategory.Q.map_id, Category.comp_id] at h1
  have h2 := Functor.mapDerivedCategoryCompIso_fac CX G P
  have hc2 : (Functor.mapHomologicalComplexCompIso (Iso.refl (CX ⋙ G))
      (.up ℤ)).hom.app P = 𝟙 _ := rfl
  erw [hc2, DerivedCategory.Q.map_id, Category.comp_id] at h2
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso CX G).inv.app
    (DerivedCategory.Q.obj P))).1
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [h1, Functor.mapDerivedCategoryNatIso_fac]
  erw [← h2]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Scheme
