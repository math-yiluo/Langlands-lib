/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-! # Coherence of scalar extension with inverse-image section cancellation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem reverse_section
    {A₀ A₁ B₀ B₁ : Type*} [Category A₀] [Category A₁]
    [Category B₀] [Category B₁]
    (E₀ : A₀ ⥤ B₀) (E₁ : A₁ ⥤ B₁) (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁)
    (adj₀ : E₀ ⊣ U₀) (adj₁ : E₁ ⊣ U₁)
    (P : A₀ ⥤ A₁) (I : A₁ ⥤ A₀) (Q : B₀ ⥤ B₁) (J : B₁ ⥤ B₀)
    (cA : P ⋙ I ≅ 𝟭 _) (cB : Q ⋙ J ≅ 𝟭 _)
    (dp : U₀ ⋙ P ⟶ Q ⋙ U₁) (di : U₁ ⋙ I ⟶ J ⋙ U₀)
    (rp : P ⋙ E₁ ⟶ E₀ ⋙ Q) (ri : I ⋙ E₀ ⟶ E₁ ⋙ J)
    (C : A₀)
    (hp : adj₁.unit.app (P.obj C) ≫ U₁.map (rp.app C) =
      P.map (adj₀.unit.app C) ≫ dp.app (E₀.obj C))
    (hi : adj₀.unit.app (I.obj (P.obj C)) ≫ U₀.map (ri.app (P.obj C)) =
      I.map (adj₁.unit.app (P.obj C)) ≫ di.app (E₁.obj (P.obj C)))
    (hd : I.map (dp.app (E₀.obj C)) ≫ di.app (Q.obj (E₀.obj C)) ≫
      U₀.map (cB.hom.app (E₀.obj C)) = cA.hom.app (U₀.obj (E₀.obj C))) :
    ri.app (P.obj C) ≫ J.map (rp.app C) ≫ cB.hom.app (E₀.obj C) =
      E₀.map (cA.hom.app C) := by
  apply (adj₀.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% hi]
  have hn := di.naturality (rp.app C)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← I.map_comp_assoc, hp, I.map_comp]
  simp only [Category.assoc]
  rw [hd]
  have hc := cA.hom.naturality (adj₀.unit.app C)
  simpa only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] using
    hc.trans (adj₀.unit.naturality (cA.hom.app C))

/-- Scalar/pullback balancing commutes with the canonical cancellation of a section. -/
theorem scalar_section_compositor
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {T S : Scheme.{u}} (i : S ⟶ T) (p : T ⟶ S) (hi : i ≫ p = 𝟙 S)
    (C : DerivedCategoryModule A S) :
    (scalarPullbackIso φ i).inv.app
        ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj C) ≫
      (upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor.map
        ((scalarPullbackIso φ p).inv.app C) ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i p hi).hom.app
        ((scalarExtension φ S).obj C) =
    (scalarExtension φ S).map
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i p hi).hom.app C) := by
  let U := Sheaf.derivedRestrictScalars S.smallEtaleTopology φ
  let aA := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
  let iA := (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
  let cA := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i p hi
  let cB := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i p hi
  have he (f : S ⟶ T) : scalarRestrictionPullbackIso φ f =
      leftDerivedUpperStarRestrictScalarsIso φ f := by
    unfold scalarRestrictionPullbackIso leftDerivedUpperStarRestrictScalarsIso
    rw [← restrictionIso_eq]
  have heP : scalarRestrictionPullbackIso φ p =
      leftDerivedUpperStarRestrictScalarsIso φ p := by
    unfold scalarRestrictionPullbackIso leftDerivedUpperStarRestrictScalarsIso
    rw [← restrictionIso_eq]
  have hd : iA.map ((scalarRestrictionPullbackIso φ p).hom.app
        ((scalarExtension φ S).obj C)) ≫
      (scalarRestrictionPullbackIso φ i).hom.app _ ≫ U.map (cB.hom.app _) =
        cA.hom.app (U.obj ((scalarExtension φ S).obj C)) := by
    rw [he i, heP]
    have hid := leftDerivedUpperStarRestrictScalarsIso_id_hom_app φ S
      ((scalarExtension φ S).obj C)
    have hcomp' := leftDerivedUpperStarRestrictScalarsIso_comp_hom_app' φ i p
      (𝟙 S) hi.symm ((scalarExtension φ S).obj C)
    apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) i p
      (𝟙 S) hi.symm).hom.app (U.obj ((scalarExtension φ S).obj C)))).1
    simp only [cA, cB, leftDerivedUpperStarCompSectionIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, U.map_comp,
      Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hcomp']
    rw [← U.map_comp_assoc]
    simp only [Iso.hom_inv_id_app, U.map_id, Category.id_comp]
    exact hid
  have hu (X Y : Scheme.{u}) (f : X ⟶ Y) (K : DerivedCategoryModule A Y) :
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
          ((scalarPullbackIso φ f).inv.app K) =
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app K) ≫
        (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ Y).obj K) := by
    have h := unit_mateEquiv_symm
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom) K
    have hr : (scalarPullbackIso φ f).inv = ProEtale.scalarPullbackReverseEtale φ f :=
      (congrArg Iso.inv (scalarPullback_eq φ f)).symm
    rw [hr]
    exact h.symm
  exact reverse_section (scalarExtension φ S) (scalarExtension φ T) U
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _) aA iA
    (upperStar (ModuleCat.{u + 1} B) p).leftDerivedFunctor
    (upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor cA cB
    (scalarRestrictionPullbackIso φ p).hom (scalarRestrictionPullbackIso φ i).hom
    (scalarPullbackIso φ p).inv (scalarPullbackIso φ i).inv C
    (hu T S p C) (hu S T i (aA.obj C)) hd

end AlgebraicGeometry.Etale
