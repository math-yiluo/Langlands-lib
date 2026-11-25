/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.Topology.Algebra.Ring.Compact
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra

/-! # The embedded coefficient diagram in the constant completion presentation

## References

* Stacks Project, Tags 099L and 093M
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option maxSynthPendingDepth 0
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint monoidal_pointUpperStar oplaxMonoidal_pointUpperStar

attribute [-instance] integralModel_coefficientMonObj

private local instance schemeCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private local instance smallCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1} := inferInstance

private local instance smallAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X) Ab.{u + 1} :=
  inferInstance

private local instance schemeAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} := inferInstance

private local instance schemeAbWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) Ab.{u + 1} := inferInstance

private local instance schemeRingWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} := inferInstance

private local instance smallAbWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X) Ab.{u + 1} :=
  inferInstance

private local instance smallRingWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1} := inferInstance

private local instance pointAbWeakSheafify :
    HasWeakSheafify (coherentTopology Profinite.{u}) Ab.{u + 1} := inferInstance

private local instance pointRingWeakSheafify :
    HasWeakSheafify (coherentTopology Profinite.{u}) CommRingCat.{u + 1} := inferInstance

-- Cache the data-bearing monoid instances before specializing coefficient rings.
private local instance pulledMonObj (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] :
    MonObj ((upperStarFromPoint X).obj R) :=
  (upperStarFromPoint X).monObjObj R

private local instance completedMonObj (X : Scheme.{u})
    (R : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}) :
    MonObj (completedCoefficient X R).X :=
  (completedCoefficient X R).mon

private def bundledSmallRing (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1} :=
  IntegralModelsStacks.smallRing X R

private def bundledSmallMap (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] : bundledSmallRing X R ⟶ bundledSmallRing X S :=
  IntegralModelsStacks.smallMap X f

private theorem coefficientMap_hom (X : Scheme.{u})
    {R S : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1}} (f : R ⟶ S) :
    (completedCoefficientMap X f).hom = (upperStarFromPoint X).map
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map f) := rfl

private theorem composeComparison {C : Type*} [Category C]
    {A B D E G H : C} {f : A ⟶ B} {eA : A ⟶ D} {eB : B ⟶ E}
    {g : D ⟶ E} {zA : D ⟶ G} {zB : E ⟶ H} {h : G ⟶ H}
    (hf : f ≫ eB = eA ≫ g) (hz : g ≫ zB = zA ≫ h) :
    f ≫ (eB ≫ zB) = (eA ≫ zA) ≫ h := by
  rw [← Category.assoc, hf, Category.assoc, hz, ← Category.assoc]

private theorem inverseComparison {C : Type*} [Category C]
    {A B D E : C} (a : A ≅ D) (b : B ≅ E) {f : D ⟶ E} {g : A ⟶ B}
    (h : a.hom ≫ f = g ≫ b.hom) : f ≫ b.inv = a.inv ≫ g := by
  apply (cancel_epi a.hom).mp
  rw [← Category.assoc a.hom f b.inv, h, Category.assoc g b.hom b.inv,
    b.hom_inv_id, Category.comp_id, a.hom_inv_id_assoc]

private theorem finiteScalarComparison {C : Type*} [Category C]
    {A B D E F G : C} {p : A ⟶ B} {q : B ⟶ D} {r : D ⟶ E}
    {m : A ⟶ F} {t : F ⟶ D} {b : F ⟶ E} {a : A ⟶ G} {g : G ⟶ E}
    (hs : p ≫ q = m ≫ t) (hc : t ≫ r = b) (hd : m ≫ b = a ≫ g) :
    p ≫ q ≫ r = a ≫ g := by
  rw [← Category.assoc p, hs, Category.assoc m, hc, hd]

private theorem cancelScalarComparison {C : Type*} [Category C]
    {A B D E F : C} {p : A ⟶ B} [Epi p] {a : B ⟶ D} {b : A ⟶ D}
    {f : B ⟶ E} {c : E ⟶ F} {h : D ⟶ F}
    (hp : p ≫ a = b) (hf : p ≫ f ≫ c = b ≫ h) : f ≫ c = a ≫ h := by
  apply (cancel_epi p).mp
  exact hf.trans ((congrArg (· ≫ h) hp.symm).trans (Category.assoc p a h))

private theorem postComparison {C : Type*} [Category C]
    {A B D E F : C} {f : A ⟶ B} {b : B ⟶ D} {a : A ⟶ E}
    {g : E ⟶ D} {z : D ⟶ F} {h : E ⟶ F}
    (hf : f ≫ b = a ≫ g) (hg : g ≫ z = h) : f ≫ b ≫ z = a ≫ h := by
  rw [← Category.assoc, hf, Category.assoc, hg]

private def smallIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (e : R ≅ S) [IsMonHom e.hom] :
    bundledSmallRing X R ≅ bundledSmallRing X S where
  hom := bundledSmallMap X e.hom
  inv := bundledSmallMap X e.inv
  hom_inv_id := by
    ext U x
    change e.inv.hom.app _ (e.hom.hom.app _ x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) e.hom_inv_id
  inv_hom_id := by
    ext U x
    change e.hom.hom.app _ (e.inv.hom.app _ x) = x
    exact congrArg (fun f ↦ f.hom.app (op (AsSmall.down.obj U.unop)) x) e.inv_hom_id

private theorem smallMap_comp (X : Scheme.{u})
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T]
    (f : R ⟶ S) (g : S ⟶ T) [IsMonHom f] [IsMonHom g] :
    bundledSmallMap X (f ≫ g) =
      bundledSmallMap X f ≫ bundledSmallMap X g := by
  ext U x
  rfl

private theorem smallMap_congr (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (f g : R ⟶ S) [IsMonHom f] [IsMonHom g] (h : f = g) :
    bundledSmallMap X f = bundledSmallMap X g := by
  subst g
  rfl

private theorem smallMap_square (X : Scheme.{u})
    {R S T U : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [MonObj T] [MonObj U]
    [IsCommMonObj R] [IsCommMonObj S] [IsCommMonObj T] [IsCommMonObj U]
    (f : R ⟶ S) (g : S ⟶ U) (h : R ⟶ T) (k : T ⟶ U)
    [IsMonHom f] [IsMonHom g] [IsMonHom h] [IsMonHom k] (w : f ≫ g = h ≫ k) :
    bundledSmallMap X f ≫ bundledSmallMap X g =
      bundledSmallMap X h ≫ bundledSmallMap X k :=
  (smallMap_comp X f g).symm.trans
    ((smallMap_congr X _ _ w).trans (smallMap_comp X h k))

private def constantPresentation
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} J
        ((Functor.const Cᵒᵖ).obj (RingCat.of.{u + 1} A)) ≅
      (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf J CommRingCat.{u + 1}).obj (CommRingCat.of.{u + 1} A))) := by
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let W := forget₂ RingCat.{u + 1} Ab.{u + 1}
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of.{u + 1} A)
  let S := (sheafCompose J V).obj ((constantSheaf J CommRingCat.{u + 1}).obj
    (CommRingCat.of.{u + 1} A))
  let φ := Functor.whiskerRight (toSheafify J P) (V ⋙ W)
  have : J.PreservesSheafification (V ⋙ W) :=
    GrothendieckTopology.instPreservesSheafification J _
  have hφ : J.W (A := Ab.{u + 1}) φ :=
    J.W_of_preservesSheafification (V ⋙ W) _ (J.W_toSheafify P)
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  exact asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso J S

private instance constantPresentation_mon
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    IsMonHom (constantPresentation J A).hom := by
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let W := forget₂ RingCat.{u + 1} Ab.{u + 1}
  let P := (Functor.const Cᵒᵖ).obj (CommRingCat.of.{u + 1} A)
  let S := (sheafCompose J V).obj ((constantSheaf J CommRingCat.{u + 1}).obj
    (CommRingCat.of.{u + 1} A))
  let ψ : ((Functor.const Cᵒᵖ).obj (RingCat.of.{u + 1} A)) ⟶ S.obj :=
    Functor.whiskerRight (toSheafify J P) V
  change IsMonHom ((presheafToSheaf J Ab.{u + 1}).map (Functor.whiskerRight ψ W) ≫
    (Sheaf.sheafifyRingPresheafIso J S).hom)
  infer_instance

attribute [local irreducible] constantPresentation

private local instance commRingSheaf_comm (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    IsCommMonObj ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :=
  Sheaf.isCommMonObj_sheafCompose_obj (Scheme.ProEt.topology X)
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
    (fun U a b ↦ @mul_comm (R.obj.obj U) inferInstance a b)

private def discretePullbackIso (X : Scheme.{u}) (A : Type) [CommRing A] :
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of.{u + 1} (ULift.{u + 1} A))))) ≅
      condensedRingObj (IntegralModelsEmbedded.discreteObj.{u} A) X := by
  let eX := @constantPresentation.{u} X.ProEt inferInstance (Scheme.ProEt.topology X)
    inferInstance inferInstance inferInstance (ULift.{u + 1} A) inferInstance
  let eP := @constantPresentation.{u} Profinite.{u} inferInstance
    (coherentTopology Profinite.{u}) inferInstance inferInstance inferInstance
    (ULift.{u + 1} A) inferInstance
  let eS := (constantSchemeIso.{u} X).app (AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A))
  exact eX.symm ≪≫ eS ≪≫ (upperStarFromPoint X).mapIso eP

private instance discretePullbackIso_mon (X : Scheme.{u}) (A : Type) [CommRing A] :
    IsMonHom (discretePullbackIso X A).hom := by
  let S := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
  let Q := constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}
  let P := upperStarFromPoint X
  let B := AddCommGrpCat.of.{u + 1} (ULift.{u + 1} A)
  let mS := Sheaf.monObj_presheafToSheaf_obj (coherentTopology Profinite.{u})
    (((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of.{u + 1} (ULift.{u + 1} A))) ⋙
      forget₂ RingCat Ab)
  let mQ := Sheaf.monObj_presheafToSheaf_obj (Scheme.ProEt.topology X)
    (((Functor.const X.ProEtᵒᵖ).obj (RingCat.of.{u + 1} (ULift.{u + 1} A))) ⋙
      forget₂ RingCat Ab)
  let transfer (m : MonObj (S.obj B)) : MonObj (P.obj (S.obj B)) :=
    @Functor.monObjObj _ _ _ _ _ _ P _ _ m
  have hi : @IsMonHom _ _ _ _ _ (transfer mS) mQ
      ((constantSchemeIso.{u} X).inv.app B) :=
    IsMonHom.of_eq (h₁ := transfer (S.monObjObj B)) (h₂ := Q.monObjObj B)
      ((constantSchemeIso.{u} X).inv.app B)
      (congrArg transfer (constantSheafRingMonObj (coherentTopology Profinite.{u})
        (ULift.{u + 1} A)))
      (constantSheafRingMonObj (Scheme.ProEt.topology X) (ULift.{u + 1} A))
      (hf := Functor.isMonHom_compAlgHom S P (constantSchemeIso.{u} X).inv B)
  have hh := monHomInvExplicit (transfer mS) mQ ((constantSchemeIso.{u} X).app B).symm hi
  have hm : IsMonHom (P.map
      (constantPresentation.{u} (coherentTopology Profinite.{u}) (ULift.{u + 1} A)).hom) :=
    inferInstance
  have hcomp := monHomCompExplicit mQ (transfer mS) _ _ _ hh hm
  have hInv : IsMonHom
      (constantPresentation.{u} (Scheme.ProEt.topology X) (ULift.{u + 1} A)).inv :=
    inferInstance
  dsimp only [discretePullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact monHomCompExplicit _ mQ _ _ _ hInv hcomp

attribute [local irreducible] discretePullbackIso

private def reconstructedIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ≅ R := by
  let J := Scheme.ProEt.topology X
  let R' := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R'
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      R'.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R'.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  apply (fullyFaithfulSheafToPresheaf J CommRingCat.{u + 1}).preimageIso
  refine NatIso.ofComponents (fun Z ↦ ?_) (fun f ↦ ?_)
  · refine RingEquiv.toCommRingCatIso
      (R := (InternalAbelianSheafModule.sectionRingSheaf J A).obj.obj Z)
      (S := R.obj.obj Z)
      { toEquiv := Equiv.refl _
        map_add' := fun _ _ ↦ rfl
        map_mul' := ?_ }
    intro a b
    change (((sheafToPresheaf J Ab.{u + 1}).monObjObj A).mul.app Z).hom
      (a ⊗ₜ[ℤ] b) = (show R.obj.obj Z from a) * (show R.obj.obj Z from b)
    have hm := congrArg (fun m : MonObj A.obj ↦ m.mul) hmon
    rw [hm]
    rfl
  · ext a
    rfl

attribute [local irreducible] reconstructedIso

private abbrev smallPushRing (X : Scheme.{u}) :=
  (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)

private instance downEquivalence (X : Scheme.{u}) :
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsEquivalence :=
  inferInstanceAs ((AsSmall.equiv (C := X.ProEt)).inverse.IsEquivalence)

private instance downDense (X : Scheme.{u}) :
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsDenseSubsite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (Scheme.ProEt.topology X) := by
  change (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).IsDenseSubsite ((AsSmall.down :
      Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology (Scheme.ProEt.topology X)) (Scheme.ProEt.topology X)
  infer_instance

private def smallConstantsIso (X : Scheme.{u}) :
    constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙ smallPushRing X ≅
      constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1} := by
  let e := (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
    X.ProEt).pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)
  exact NatIso.ofComponents
    (fun A ↦ e.symm.app ((Functor.const X.ProEtᵒᵖ).obj A)) (by
      intro A B f
      exact e.inv.naturality ((Functor.const X.ProEtᵒᵖ).map f))

attribute [local irreducible] smallConstantsIso bundledSmallMap

private def discreteSmallIso (X : Scheme.{u}) (A : Type) [CommRing A] :
    bundledSmallRing X
        (condensedRingObj (IntegralModelsEmbedded.discreteObj.{u} A) X) ≅
      ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} A) :=
  (smallIso X (discretePullbackIso X A)).symm ≪≫
    (smallPushRing X).mapIso
      (reconstructedIso X ((constantSheaf (Scheme.ProEt.topology X)
        CommRingCat.{u + 1}).obj (CommRingCat.of.{u + 1} (ULift.{u + 1} A)))) ≪≫
    (smallConstantsIso X).app (CommRingCat.of.{u + 1} (ULift.{u + 1} A))

private theorem constantPresentation_naturality
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [HasSheafify J CommRingCat.{u + 1}]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (f : A →+* B) :
    (constantSheaf J Ab.{u + 1}).map (AddCommGrpCat.ofHom f.toAddMonoidHom) ≫
        (constantPresentation J B).hom =
      (constantPresentation J A).hom ≫
        (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            ((constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom f))) := by
  unfold constantPresentation
  let L := presheafToSheaf J Ab.{u + 1}
  let g := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom f)))
  have hn := (sheafificationAdjunction J Ab.{u + 1}).counit.naturality g
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  change L.map _ ≫ (L.map _ ≫ (sheafificationAdjunction J Ab.{u + 1}).counit.app _) =
    (L.map _ ≫ (sheafificationAdjunction J Ab.{u + 1}).counit.app _) ≫ g
  erw [← Category.assoc, ← L.map_comp]
  erw [Category.assoc, ← hn, ← Category.assoc, ← L.map_comp]
  apply congrArg (fun h ↦ L.map h ≫
    (sheafificationAdjunction J Ab.{u + 1}).counit.app _)
  have h := toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f))
  ext U x
  exact congrArg (fun h ↦ (h.app U).hom x) h

private theorem discretePullbackIso_naturality (X : Scheme.{u})
    {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf _ CommRingCat.{u + 1}).map (CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom))))) ≫
        (discretePullbackIso X B).hom =
      (discretePullbackIso X A).hom ≫
        (upperStarFromPoint X).map (IntegralModelsEmbedded.discreteMap f) := by
  let a : ULift.{u + 1} A →+* ULift.{u + 1} B :=
    ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)
  have hX := constantPresentation_naturality.{u} (Scheme.ProEt.topology X) a
  have hP := constantPresentation_naturality.{u} (coherentTopology Profinite.{u}) a
  have hS := (constantSchemeIso.{u} X).hom.naturality
    (AddCommGrpCat.ofHom a.toAddMonoidHom)
  unfold discretePullbackIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  apply (cancel_epi (constantPresentation.{u} (Scheme.ProEt.topology X)
    (ULift.{u + 1} A)).hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  erw [← reassoc_of% hX, Iso.hom_inv_id_assoc]
  erw [← Category.assoc, hS, Category.assoc]
  dsimp only [Functor.comp_map]
  erw [← Functor.map_comp, hP, Functor.map_comp]
  rfl

private theorem discreteSmallIso_naturality (X : Scheme.{u})
    {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    bundledSmallMap X
        ((upperStarFromPoint X).map (IntegralModelsEmbedded.discreteMap f)) ≫
        (discreteSmallIso X B).hom =
      (discreteSmallIso X A).hom ≫
        (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          CommRingCat.{u + 1}).map (CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom))) := by
  let C := constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}
  let a := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  let P := smallPushRing X
  let rA := reconstructedIso X (C.obj (CommRingCat.of.{u + 1} (ULift.{u + 1} A)))
  let rB := reconstructedIso X (C.obj (CommRingCat.of.{u + 1} (ULift.{u + 1} B)))
  let dA := smallIso X (discretePullbackIso X A)
  let dB := smallIso X (discretePullbackIso X B)
  have hn : dA.hom ≫ bundledSmallMap X
      ((upperStarFromPoint X).map (IntegralModelsEmbedded.discreteMap f)) =
      bundledSmallMap X
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (C.map a))) ≫ dB.hom := by
    change bundledSmallMap X (discretePullbackIso X A).hom ≫ _ =
      _ ≫ bundledSmallMap X (discretePullbackIso X B).hom
    exact smallMap_square X _ _ _ _ (discretePullbackIso_naturality X f).symm
  have hr : bundledSmallMap X
      ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (C.map a))) ≫ P.map rB.hom = P.map rA.hom ≫ P.map (C.map a) := by
    ext U x
    unfold bundledSmallMap
    dsimp only [rA, rB, P]
    unfold reconstructedIso
    rfl
  have hd := inverseComparison dA dB hn
  have hR := composeComparison hd hr
  have hC := (smallConstantsIso X).hom.naturality a
  dsimp only [Functor.comp_map] at hC
  have hS := composeComparison hR hC
  dsimp only [discreteSmallIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  dsimp only [dA, dB, rA, rB, P, C, a] at hS
  simpa only [Category.assoc, Iso.app_hom] using hS

attribute [local irreducible] discreteSmallIso bundledSmallRing

private theorem scalarPoint_naturality {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    IntegralModelsEmbedded.discreteMap f ≫
        (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous B) =
      (sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous A) ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMap f hf) := by
  let J := coherentTopology Profinite.{u}
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let W := sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})
  change W.map _ ≫ W.map _ = W.map _ ≫ W.map _
  rw [← W.map_comp, ← W.map_comp]
  apply congrArg W.map
  let a := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hn := (constantCommuteCompose J V).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  unfold IntegralModelsEmbedded.constantToContinuous
  erw [← Category.assoc, hn]
  simp only [Category.assoc]
  apply congrArg (((constantCommuteCompose J V).hom.app
    (CommRingCat.of.{u + 1} (ULift.{u + 1} A))) ≫ ·)
  dsimp only [constantSheaf, Functor.comp_map]
  erw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1

private theorem constantPresentation_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J Ab.{u + 1}] [(J.W (A := Ab.{u + 1})).IsMonoidal]
    [HasSheafify J CommRingCat.{u + 1}]
    (A : Type (u + 1)) [CommRing A] :
    toSheafify J ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of.{u + 1} A)) ≫
        (constantPresentation J A).hom.hom =
      Functor.whiskerRight
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of.{u + 1} A)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1}) := by
  unfold constantPresentation
  exact ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _

private theorem constantCommuteCompose_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (A : Type (u + 1)) [CommRing A] :
    Functor.whiskerRight
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of.{u + 1} A)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ≫
        ((constantCommuteCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app
          (CommRingCat.of.{u + 1} A)).hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of.{u + 1} A)) := by
  rw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
    sheafComposeIso_inv_fac, ← toSheafify_naturality]
  ext U x
  rfl

private noncomputable def finitePointComparison (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [DiscreteTopology R] [Finite R] :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} R))) ≅
      Profinite.continuousMapRingObj R := by
  let J := coherentTopology Profinite.{u}
  let φ := Functor.whiskerRight (Profinite.constantToContinuousRing.{u} R)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have hφ : J.W (A := Ab.{u + 1}) φ := J.W_of_isLocallyBijective φ
  have : IsIso ((presheafToSheaf J Ab.{u + 1}).map φ) := (J.W_iff φ).mp hφ
  exact asIso ((presheafToSheaf J Ab.{u + 1}).map φ) ≪≫
    Sheaf.sheafifyRingPresheafIso.{u + 1, u, u + 1} J (Profinite.continuousMapRingSheaf R)

private instance finitePoint_isIso (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    IsIso ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (IntegralModelsEmbedded.constantToContinuous A)) := by
  let J := coherentTopology Profinite.{u}
  let V := forget₂ CommRingCat.{u + 1} RingCat.{u + 1}
  let W := forget₂ RingCat.{u + 1} Ab.{u + 1}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj (CommRingCat.of.{u + 1} (ULift.{u + 1} A))
  have h : (constantPresentation J (ULift.{u + 1} A)).hom ≫
      (sheafCompose J W).map (IntegralModelsEmbedded.constantToContinuous A) =
      (finitePointComparison.{u} A).hom := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ (Profinite.continuousMapRingObj A).property
    change toSheafify J _ ≫ (constantPresentation J (ULift.{u + 1} A)).hom.hom ≫
      Functor.whiskerRight (IntegralModelsEmbedded.constantToContinuous A).hom W = _
    erw [← Category.assoc, constantPresentation_unit]
    unfold IntegralModelsEmbedded.constantToContinuous
    erw [Functor.whiskerRight_comp, ← Category.assoc]
    have hu := congrArg (fun h ↦ Functor.whiskerRight h W)
      (constantCommuteCompose_unit J (ULift.{u + 1} A))
    simp only [Functor.whiskerRight_comp] at hu
    erw [hu]
    have hR := ((sheafificationAdjunction J RingCat.{u + 1}).homEquiv _
      (Profinite.continuousMapRingSheaf A)).apply_symm_apply
      (Profinite.constantToContinuousRing.{u} A)
    have hA := ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _
      (Profinite.continuousMapRingObj A)).apply_symm_apply
      (Functor.whiskerRight (Profinite.constantToContinuousRing.{u} A) W)
    exact (congrArg (fun h ↦ Functor.whiskerRight h W) hR).trans hA.symm
  have : IsIso ((constantPresentation J (ULift.{u + 1} A)).hom ≫
      (sheafCompose J W).map (IntegralModelsEmbedded.constantToContinuous A)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (constantPresentation J (ULift.{u + 1} A)).hom _

private def smallForget (X : Scheme.{u}) :=
  sheafToPresheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})

private def smallUnderlyingIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] :
    (smallForget X).obj (bundledSmallRing X R) ≅
      ((Functor.whiskeringLeft _ _ _).obj
        (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op).obj
          R.obj := by
  unfold smallForget bundledSmallRing
  exact Iso.refl _

private def reflectSmallLimit (X : Scheme.{u})
    {T : ℕᵒᵖ ⥤ Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}} (c : Cone T)
    (hc : IsLimit ((smallForget X).mapCone c)) : IsLimit c := by
  have : (forget₂ RingCat.{u + 1} Ab.{u + 1}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : PreservesLimitsOfSize.{u + 1, u + 1}
      (forget₂ RingCat.{u + 1} Ab.{u + 1}) :=
    preservesLimitsOfSize_of_univLE.{u + 1, u + 1} _
  have : PreservesLimitsOfShape ℕᵒᵖ (smallForget X) := by
    dsimp only [smallForget]
    infer_instance
  have : (smallForget X).ReflectsIsomorphisms := by
    dsimp only [smallForget]
    infer_instance
  have : ReflectsLimitsOfShape ℕᵒᵖ (smallForget X) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact isLimitOfReflects (smallForget X) hc

private def continuousSmallIso (X : Scheme.{u}) (A : Type) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [Finite A] [DiscreteTopology A] :
    bundledSmallRing X
        (condensedRingObj (Profinite.continuousMapRingObj A) X) ≅
      ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} A) := by
  let f := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (IntegralModelsEmbedded.constantToContinuous A)
  have : IsIso f := finitePoint_isIso A
  have : IsMonHom f := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (IntegralModelsEmbedded.constantToContinuous A)
  have : IsMonHom ((upperStarFromPoint X).mapIso (asIso f)).hom := by
    change IsMonHom ((upperStarFromPoint X).map f)
    infer_instance
  exact (smallIso X ((upperStarFromPoint X).mapIso (asIso f))).symm ≪≫
    discreteSmallIso X A

private theorem continuousSmallIso_scalar (X : Scheme.{u})
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A] :
    bundledSmallMap X
        ((upperStarFromPoint X).map
          ((sheafCompose (coherentTopology Profinite.{u})
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (IntegralModelsEmbedded.constantToContinuous A))) ≫
        (continuousSmallIso X A).hom = (discreteSmallIso X A).hom := by
  let f := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (IntegralModelsEmbedded.constantToContinuous A)
  have : IsIso f := finitePoint_isIso A
  have : IsMonHom f := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (IntegralModelsEmbedded.constantToContinuous A)
  have : IsMonHom ((upperStarFromPoint X).mapIso (asIso f)).hom := by
    change IsMonHom ((upperStarFromPoint X).map f)
    infer_instance
  let e := smallIso X ((upperStarFromPoint X).mapIso (asIso f))
  change e.hom ≫ (e.inv ≫ (discreteSmallIso X A).hom) = _
  exact e.hom_inv_id_assoc _

private theorem scalarToFiniteComparison (X : Scheme.{u})
    {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [Finite B] [DiscreteTopology B] (f : A →+* B) (hf : Continuous f) :
    bundledSmallMap X ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous A))) ≫
      bundledSmallMap X
        (completedCoefficientMap X (Profinite.continuousMapRingSheafMap f hf)).hom ≫
        (continuousSmallIso X B).hom =
      (discreteSmallIso X A).hom ≫
        (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          CommRingCat.{u + 1}).map (CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom))) := by
  have hs : bundledSmallMap X ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous A))) ≫
      bundledSmallMap X
        (completedCoefficientMap X (Profinite.continuousMapRingSheafMap f hf)).hom =
      bundledSmallMap X
        ((upperStarFromPoint X).map (IntegralModelsEmbedded.discreteMap f)) ≫
      bundledSmallMap X ((upperStarFromPoint X).map
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (IntegralModelsEmbedded.constantToContinuous B))) := by
    apply smallMap_square X
    have h := congrArg (upperStarFromPoint X).map (scalarPoint_naturality f hf)
    simpa only [coefficientMap_hom, Functor.map_comp] using h.symm
  exact finiteScalarComparison hs (continuousSmallIso_scalar X B)
    (discreteSmallIso_naturality X f)

private theorem continuousSmallIso_naturality (X : Scheme.{u})
    {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    [Finite A] [DiscreteTopology A] [Finite B] [DiscreteTopology B]
    (f : A →+* B) (hf : Continuous f) :
    bundledSmallMap X
        (completedCoefficientMap X (Profinite.continuousMapRingSheafMap f hf)).hom ≫
        (continuousSmallIso X B).hom =
      (continuousSmallIso X A).hom ≫
        (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          CommRingCat.{u + 1}).map (CommRingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom))) := by
  let g := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (IntegralModelsEmbedded.constantToContinuous A)
  have : IsIso g := finitePoint_isIso A
  have : IsMonHom g := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (IntegralModelsEmbedded.constantToContinuous A)
  have : IsMonHom ((upperStarFromPoint X).mapIso (asIso g)).hom := by
    change IsMonHom ((upperStarFromPoint X).map g)
    infer_instance
  let e := smallIso X ((upperStarFromPoint X).mapIso (asIso g))
  have : IsIso (bundledSmallMap X ((upperStarFromPoint X).map g)) := by
    change IsIso e.hom
    infer_instance
  exact cancelScalarComparison (continuousSmallIso_scalar X A)
    (scalarToFiniteComparison X f hf)

attribute [local irreducible] continuousSmallIso

private def quotientLiftIso (A : Type) [CommRing A] (π : A) (n : ℕ) :
    ULift.{u + 1} (A ⧸ (Ideal.span {π}) ^ (n + 1)) ≃+*
      ULift.{u + 1} A ⧸ (Ideal.span {ULift.up π}) ^ (n + 1) :=
  ULift.ringEquiv.trans
    (Ideal.quotientEquiv _ _ (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm (by
      rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
      rfl))

private theorem quotientLiftIso_mk (A : Type) [CommRing A] (π x : A) (n : ℕ) :
    quotientLiftIso A π n (ULift.up (Ideal.Quotient.mk _ x)) =
      Ideal.Quotient.mk _ (ULift.up x) := rfl

private def quotientLiftRingIso (A : Type) [CommRing A] (π : A) (n : ℕ) :
    CommRingCat.of (ULift.{u + 1} (A ⧸ (Ideal.span {π}) ^ (n + 1))) ≅
      CommRingCat.of (ULift.{u + 1} A ⧸ (Ideal.span {ULift.up π}) ^ (n + 1)) :=
  RingEquiv.toCommRingCatIso (quotientLiftIso A π n)

private theorem quotientLiftIso_factor (A : Type) [CommRing A] (π : A) (n : ℕ) :
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1))).comp
        ULift.ringEquiv.toRingHom)) ≫
        (quotientLiftRingIso A π n).hom =
      (quotientLiftRingIso A π (n + 1)).hom ≫
        CommRingCat.ofHom
          (R := ULift.{u + 1} A ⧸ (Ideal.span {ULift.up π}) ^ (n + 1 + 1))
          (S := ULift.{u + 1} A ⧸ (Ideal.span {ULift.up π}) ^ (n + 1))
          (Ideal.Quotient.factorPow
            (Ideal.span {ULift.up.{u + 1} π}) (Nat.le_succ (n + 1))) := by
  ext x
  obtain ⟨x⟩ := x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

private theorem quotientLiftIso_quotient (A : Type) [CommRing A] (π : A) (n : ℕ) :
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))).comp
        ULift.ringEquiv.toRingHom)) ≫
        (quotientLiftRingIso A π n).hom =
      CommRingCat.ofHom (R := ULift.{u + 1} A)
        (S := ULift.{u + 1} A ⧸ (Ideal.span {ULift.up π}) ^ (n + 1))
        (Ideal.Quotient.mk ((Ideal.span {ULift.up.{u + 1} π}) ^ (n + 1))) := by
  ext x
  exact quotientLiftIso_mk A π x.down n

attribute [local irreducible] quotientLiftRingIso

private theorem discreteSmallIso_quotient (X : Scheme.{u})
    (A : Type) [CommRing A] (π : A) (n : ℕ) :
    bundledSmallMap X ((upperStarFromPoint X).map
        (IntegralModelsEmbedded.discreteMap
          (Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))))) ≫
        ((discreteSmallIso X (A ⧸ (Ideal.span {π}) ^ (n + 1))).hom ≫
          (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
            CommRingCat.{u + 1}).map
              (quotientLiftRingIso A π n).hom) =
      (discreteSmallIso X A).hom ≫
        ConstantCompletion.quotient (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} A) (Ideal.span {ULift.up π}) n := by
  let K := constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    CommRingCat.{u + 1}
  let f := Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))
  let g := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  let e := (quotientLiftRingIso A π n).hom
  have hq : K.map g ≫ K.map e =
      ConstantCompletion.quotient (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} A) (Ideal.span {ULift.up π}) n :=
    (K.map_comp g e).symm.trans (congrArg K.map (quotientLiftIso_quotient A π n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ K.map e) (discreteSmallIso_naturality X f)).trans
      ((Category.assoc _ _ _).trans (congrArg ((discreteSmallIso X A).hom ≫ ·) hq)))

private def continuousTower (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E) :
    ℕᵒᵖ ⥤ Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ bundledSmallRing X
      (completedCoefficient X (Profinite.continuousMapRingSheaf
        (completedResidue ℓ E π n))).X)
    (fun n ↦ bundledSmallMap X
      (completedCoefficientMap X (completedResidueTransition ℓ E π n)).hom)

private theorem completedReduction_comp (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E) (n : ℕ) :
    (completedCoefficientMap X (completedReduction ℓ E π (n + 1))).hom ≫
      (completedCoefficientMap X (completedResidueTransition ℓ E π n)).hom =
        (completedCoefficientMap X (completedReduction ℓ E π n)).hom := by
  simp only [coefficientMap_hom]
  rw [← Functor.map_comp]
  congr 1

private theorem smallReduction_comp (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E) (n : ℕ) :
    bundledSmallMap X
        (completedCoefficientMap X (completedReduction ℓ E π (n + 1))).hom ≫
      bundledSmallMap X
        (completedCoefficientMap X (completedResidueTransition ℓ E π n)).hom =
      bundledSmallMap X
        (completedCoefficientMap X (completedReduction ℓ E π n)).hom := by
  have h := smallMap_comp X
    (completedCoefficientMap X (completedReduction ℓ E π (n + 1))).hom
    (completedCoefficientMap X (completedResidueTransition ℓ E π n)).hom
  refine h.symm.trans ?_
  congr 1
  exact completedReduction_comp X ℓ E π n

private def continuousCone (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E) :
    Cone (continuousTower X ℓ E π) where
  pt := bundledSmallRing X
    (completedCoefficient X (Profinite.padicIntegersCondensedRing ℓ E)).X
  π := NatTrans.ofOpSequence (fun n ↦ bundledSmallMap X
    (completedCoefficientMap X (completedReduction ℓ E π n)).hom) (by
      intro n
      simp only [Functor.const_obj_map, continuousTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (Category.id_comp
        (bundledSmallMap X
          (completedCoefficientMap X (completedReduction ℓ E π n)).hom)).trans
        (smallReduction_comp X ℓ E π n).symm)

private theorem continuousConeLimit (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E)) :
    Nonempty (IsLimit (continuousCone X ℓ E π)) := by
  obtain ⟨c, e, he, ⟨hc⟩⟩ := (completedCondensedIntegral X ℓ E π hπ).1
  let U := Mon.forget (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  let W := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op
  let T₀ := Functor.ofOpSequence
    (X := fun n ↦ completedCoefficient X
      (Profinite.continuousMapRingSheaf (completedResidue ℓ E π n)))
    (fun n ↦ completedCoefficientMap X (completedResidueTransition ℓ E π n))
  have hu := isLimitOfPreserves (U ⋙ W) hc
  let e₀ (n : ℕᵒᵖ) := smallUnderlyingIso X
    (completedCoefficient X
      (Profinite.continuousMapRingSheaf (completedResidue ℓ E π n.unop))).X
  let β : continuousTower X ℓ E π ⋙ smallForget X ≅ T₀ ⋙ U ⋙ W :=
    NatIso.ofComponents e₀ (by
      let τ : continuousTower X ℓ E π ⋙ smallForget X ⟶ T₀ ⋙ U ⋙ W :=
        NatTrans.ofOpSequence (fun n ↦ (e₀ (op n)).hom) (by
          intro n
          simp only [Functor.comp_map, continuousTower, T₀,
            Functor.ofOpSequence_map_homOfLE_succ]
          ext V x
          unfold e₀ smallUnderlyingIso bundledSmallMap
          rfl)
      intro n m f
      exact τ.naturality f)
  let ep := smallUnderlyingIso X
    (completedCoefficient X (Profinite.padicIntegersCondensedRing ℓ E)).X
  have hl : IsLimit ((smallForget X).mapCone (continuousCone X ℓ E π)) :=
    (IsLimit.equivOfNatIsoOfIso β
      ((smallForget X).mapCone (continuousCone X ℓ E π)) ((U ⋙ W).mapCone c)
      (Cone.ext (ep ≪≫ (U ⋙ W).mapIso e) (by
        intro n
        have h := congrArg (fun f ↦ W.map (U.map f)) (he n.unop).symm
        simp only [Functor.map_comp] at h
        ext V x
        dsimp only [Functor.mapCone, Cone.postcompose, continuousCone,
          Functor.const_obj_obj] at x
        unfold smallForget bundledSmallRing at x
        dsimp only [Functor.mapCone, Cone.postcompose, β, continuousCone,
          NatIso.ofComponents, NatTrans.ofOpSequence]
        unfold ep e₀ smallUnderlyingIso bundledSmallMap
        exact congrArg (fun f ↦ f.app V x) h))).symm hu
  exact ⟨reflectSmallLimit X _ hl⟩

private def residueSmallIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    [∀ n, Finite (completedResidue ℓ E π n)]
    [∀ n, DiscreteTopology (completedResidue ℓ E π n)] (n : ℕ) :
    bundledSmallRing X
        (completedCoefficient X
          (Profinite.continuousMapRingSheaf (completedResidue ℓ E π n))).X ≅
      ConstantCompletion.finite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) n :=
  continuousSmallIso X (completedResidue ℓ E π n) ≪≫
    (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}).mapIso (quotientLiftRingIso (PadicAlgCl.integers ℓ E) π n)

private theorem residueSmallIso_transition (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    [∀ n, Finite (completedResidue ℓ E π n)]
    [∀ n, DiscreteTopology (completedResidue ℓ E π n)] (n : ℕ) :
    bundledSmallMap X
        (completedCoefficientMap X (completedResidueTransition ℓ E π n)).hom ≫
        (residueSmallIso X ℓ E π n).hom =
      (residueSmallIso X ℓ E π (n + 1)).hom ≫
        ConstantCompletion.transition (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) n := by
  let f := Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1))
  have hn := continuousSmallIso_naturality X f (show Continuous f from
    continuous_of_discreteTopology)
  let K := constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    CommRingCat.{u + 1}
  let g := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  have hq : K.map g ≫ K.map (quotientLiftRingIso (PadicAlgCl.integers ℓ E) π n).hom =
      K.map (quotientLiftRingIso (PadicAlgCl.integers ℓ E) π (n + 1)).hom ≫
      ConstantCompletion.transition (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) n := by
    exact (K.map_comp g _).symm.trans
      ((congrArg K.map (quotientLiftIso_factor (PadicAlgCl.integers ℓ E) π n)).trans
        (K.map_comp _ _))
  dsimp only [residueSmallIso, Iso.trans_hom, Functor.mapIso_hom]
  exact composeComparison hn hq

private theorem residueSmallIso_scalar (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    [∀ n, Finite (completedResidue ℓ E π n)]
    [∀ n, DiscreteTopology (completedResidue ℓ E π n)] (n : ℕ) :
    bundledSmallMap X (IntegralModelsEmbedded.scalarMap ℓ E X) ≫
        bundledSmallMap X
          (completedCoefficientMap X (completedReduction ℓ E π n)).hom ≫
        (residueSmallIso X ℓ E π n).hom =
      (discreteSmallIso X (PadicAlgCl.integers ℓ E)).hom ≫
        ConstantCompletion.quotient (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) n := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let f := Ideal.Quotient.mk ((Ideal.span {π}) ^ (n + 1))
  have hf := scalarToFiniteComparison X (A := PadicAlgCl.integers ℓ E)
    (B := completedResidue ℓ E π n) f continuous_quot_mk
  let K := constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    CommRingCat.{u + 1}
  let g : CommRingCat.of (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) ⟶
      CommRingCat.of (ULift.{u + 1} (completedResidue ℓ E π n)) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    (f.comp ULift.ringEquiv.toRingHom))
  let e := K.mapIso (quotientLiftRingIso (PadicAlgCl.integers ℓ E) π n)
  have hq : K.map g ≫ e.hom =
      ConstantCompletion.quotient (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) n :=
    (K.map_comp g _).symm.trans
      (congrArg K.map (quotientLiftIso_quotient (PadicAlgCl.integers ℓ E) π n))
  have hp := postComparison hf hq
  dsimp only [f, K, g, e, Functor.mapIso_hom] at hp
  simpa only [residueSmallIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
    IntegralModelsEmbedded.scalarMap, IntegralModelsEmbedded.scalarPointMap,
    completedReduction] using hp

attribute [local irreducible] residueSmallIso
attribute [instance] integralModel_coefficientMonObj

attribute [local semireducible] bundledSmallMap bundledSmallRing
attribute [-instance] pulledMonObj completedMonObj

private theorem completedResidue_finite (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) (n : ℕ) :
    Finite (completedResidue ℓ E π n) :=
  (completedCondensedIntegral X ℓ E π hπ).2.1 n

private theorem completedResidue_discrete (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) (n : ℕ) :
    DiscreteTopology (completedResidue ℓ E π n) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  let R := PadicAlgCl.integers ℓ E
  let : CompactSpace R := PadicAlgCl.compactSpace_integers ℓ E.1
  apply QuotientAddGroup.discreteTopology
  change IsOpen (X := R) ↑((Ideal.span {π}) ^ (n + 1))
  rw [hπ]
  exact IsLocalRing.isOpen_maximalIdeal_pow R (n + 1)

private def residueTowerIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E)
    [∀ n, Finite (completedResidue ℓ E π n)]
    [∀ n, DiscreteTopology (completedResidue ℓ E π n)] :
    continuousTower X ℓ E π ≅ ConstantCompletion.finiteSystem
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) :=
  let τ : continuousTower X ℓ E π ⟶ ConstantCompletion.finiteSystem
      (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      (ULift.{u + 1} (PadicAlgCl.integers ℓ E)) (Ideal.span {ULift.up π}) :=
    NatTrans.ofOpSequence (fun n ↦ (residueSmallIso X ℓ E π n).hom) (by
      intro n
      dsimp only [continuousTower]
      simp only [Functor.ofOpSequence_map_homOfLE_succ,
        ConstantCompletion.finiteSystem]
      exact residueSmallIso_transition X ℓ E π n)
  NatIso.ofComponents (fun n ↦ residueSmallIso X ℓ E π n.unop) (fun f ↦ τ.naturality f)

attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded discrete coefficient ring is the constant sheaf on the integer ring:
constant inverse image, the monoidal constant-sheaf comparison, section-ring
reconstruction and precomposition with `AsSmall`. -/
@[no_expose] def integralModelsEmbeddedConstantIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (X : Scheme.{u}) :
    (Arrow.mk (IntegralModelsStacks.smallMap X
        (IntegralModelsEmbedded.scalarMap ℓ E X))).left ≅
      ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) :=
  discreteSmallIso X (PadicAlgCl.integers ℓ E)

attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded completed coefficient ring is the constant completion: the comparison of
the embedded integral limit cone with the limit of the constant finite system, through the
finite constant comparisons `residueSmallIso`. -/
@[no_expose] def integralModelsEmbeddedCompletedIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) :
    (Arrow.mk (IntegralModelsStacks.smallMap X
        (IntegralModelsEmbedded.scalarMap ℓ E X))).right ≅
      ConstantCompletion.completed (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) :=
  haveI := completedResidue_finite X ℓ E π hπ
  haveI := completedResidue_discrete ℓ E π hπ
  (continuousConeLimit X ℓ E π hπ).some.conePointsIsoOfNatIso
    (limit.isLimit _) (residueTowerIso X ℓ E π)

attribute [-instance] integralModel_coefficientMonObj in
/-- The embedded first residue ring is the constant sheaf on the first quotient: the
discrete comparison followed by the quotient-lift ring isomorphism. -/
@[no_expose] def integralModelsEmbeddedResidueIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    (Arrow.mk (IntegralModelsStacks.smallMap X
        (IntegralModelsEmbedded.residueMap ℓ E π X))).right ≅
      ConstantCompletion.finite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) 0 :=
  discreteSmallIso X (completedResidue ℓ E π 0) ≪≫
    (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
      CommRingCat.{u + 1}).mapIso (quotientLiftRingIso (PadicAlgCl.integers ℓ E) π 0)

attribute [-instance] integralModel_coefficientMonObj in
/-- The completed first residue ring is the constant sheaf on the first quotient: the
finite constant comparison `residueSmallIso` at level zero. -/
@[no_expose] def integralModelsEmbeddedReductionIso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) :
    (Arrow.mk (IntegralModelsStacks.smallMap X
        (completedCoefficientMap X (completedReduction ℓ E π 0)).hom)).right ≅
      ConstantCompletion.finite (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) 0 :=
  haveI := completedResidue_finite X ℓ E π hπ
  haveI := completedResidue_discrete ℓ E π hπ
  residueSmallIso X ℓ E π 0

private theorem integralModelsEmbeddedCompletedIso_hom_projection
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) [∀ n, Finite (completedResidue ℓ E π n)]
    [∀ n, DiscreteTopology (completedResidue ℓ E π n)] (n : ℕ) :
    (integralModelsEmbeddedCompletedIso ℓ E π hπ X).hom ≫
        ConstantCompletion.projection (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) n =
      bundledSmallMap X (completedCoefficientMap X (completedReduction ℓ E π n)).hom ≫
        (residueSmallIso X ℓ E π n).hom :=
  (continuousConeLimit X ℓ E π hπ).some.conePointsIsoOfNatIso_hom_comp
    (limit.isLimit _) (residueTowerIso X ℓ E π) (op n)

attribute [-instance] integralModel_coefficientMonObj in
/-- The scalar square of the embedded completion diagram: the prescribed embedded scalar
and residue maps identify with the canonical constant
completion diagram. This assertion identifies coefficient rings and maps only; it contains
no assertion about kernels, generators, surjectivity, flatness, or module categories. -/
theorem integralModelsEmbedded_scalar_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) :
    IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.scalarMap ℓ E X) ≫
        (integralModelsEmbeddedCompletedIso ℓ E π hπ X).hom =
      (integralModelsEmbeddedConstantIso ℓ E X).hom ≫
        ConstantCompletion.coefficientMap (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) := by
  have := completedResidue_finite X ℓ E π hπ
  have := completedResidue_discrete ℓ E π hπ
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let A := ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)
  let I : Ideal A := Ideal.span {ULift.up π}
  let b := integralModelsEmbeddedCompletedIso ℓ E π hπ X
  let a := integralModelsEmbeddedConstantIso ℓ E X
  have hb (n : ℕ) := integralModelsEmbeddedCompletedIso_hom_projection ℓ E π hπ X n
  apply limit.hom_ext
  intro n
  change _ ≫ ConstantCompletion.projection J A I n.unop =
    _ ≫ ConstantCompletion.projection J A I n.unop
  let φ := bundledSmallMap X (IntegralModelsEmbedded.scalarMap ℓ E X)
  have hp : ConstantCompletion.coefficientMap J A I ≫
      ConstantCompletion.projection J A I n.unop =
      ConstantCompletion.quotient J A I n.unop :=
    limit.lift_π (ConstantCompletion.quotientCone J A I) n
  exact (Category.assoc φ b.hom _).trans
    ((congrArg (φ ≫ ·) (hb n.unop)).trans
      ((residueSmallIso_scalar X ℓ E π n.unop).trans
        ((congrArg (a.hom ≫ ·) hp.symm).trans (Category.assoc _ _ _).symm)))

attribute [-instance] integralModel_coefficientMonObj in
/-- The residue square of the embedded completion diagram. -/
theorem integralModelsEmbedded_residue_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1) (X : Scheme.{u}) :
    IntegralModelsStacks.smallMap X (IntegralModelsEmbedded.residueMap ℓ E π X) ≫
        (integralModelsEmbeddedResidueIso ℓ E π X).hom =
      (integralModelsEmbeddedConstantIso ℓ E X).hom ≫
        ConstantCompletion.quotient (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) 0 :=
  discreteSmallIso_quotient X (PadicAlgCl.integers ℓ E) π 0

attribute [-instance] integralModel_coefficientMonObj in
/-- The reduction square of the embedded completion diagram: level zero of the projection
equations of `integralModelsEmbeddedCompletedIso`. -/
theorem integralModelsEmbedded_reduction_square
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (X : Scheme.{u}) :
    IntegralModelsStacks.smallMap X
        (completedCoefficientMap X (completedReduction ℓ E π 0)).hom ≫
        (integralModelsEmbeddedReductionIso ℓ E π hπ X).hom =
      (integralModelsEmbeddedCompletedIso ℓ E π hπ X).hom ≫
        ConstantCompletion.projection (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          (ULift.{u + 1} (PadicAlgCl.integers ℓ E.1)) (Ideal.span {ULift.up π}) 0 := by
  have := completedResidue_finite X ℓ E π hπ
  have := completedResidue_discrete ℓ E π hπ
  exact (integralModelsEmbeddedCompletedIso_hom_projection ℓ E π hπ X 0).symm

end AlgebraicGeometry.ProEtale
