/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientSectionAction
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRingComparison
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Compatibility of the normalized coefficient map with direct image

Source: diagonal coefficient changes, paragraph (1), integral coefficient comparison.
(blueprint: lem-sfb-diagonal-completed-scalar-push).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint condensedPushforwardHom purZlResidueTowerIso
  purZlConstantPullbackIso
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

/-- The actual completed coefficient direct-image map, evaluated using its action on one.
Source: definition of completed ringed direct image
(blueprint: lem-sfb-diagonal-completed-scalar-push). -/
def completedPushScalar {l : ℕ} [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U) :
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj
      ((Scheme.proEtaleBaseChange f).op.obj U) :=
  let T := (diagonalTracePush l f).obj (SheafOfModules.unit
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
  @SMul.smul _ (T.val.obj U) inferInstance a
    (1 : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj
      ((Scheme.proEtaleBaseChange f).op.obj U))

/-- The condensed direct-image coefficient map evaluated on sections.
Source: the canonical direct-image coefficient morphism
(blueprint: lem-sfb-diagonal-completed-scalar-push). -/
def condensedPushScalarSection {l : ℕ} [Fact l.Prime] {X S : Scheme.{u}}
    (f : X ⟶ S) (U : S.ProEtᵒᵖ)
    (a : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S).obj.obj U) :
    (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj
      ((Scheme.proEtaleBaseChange f).op.obj U) :=
  CategoryTheory.SheafModuleSection.pushScalar (Scheme.proEtaleBaseChange f)
    (condensedPushforwardHom (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) U a

private theorem constant_cyclic_ext (X : Scheme.{u}) (n : ℕ)
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (g h : (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1} (ZMod n)))) ⟶ R) : g = h := by
  apply (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  apply (cancel_epi (sfbConstantRingAbIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod n)))).inv).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R).property
  ext U a
  have he : (g.hom.app U).hom.comp
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod n))))).app U).hom) =
      (h.hom.app U).hom.comp
      (((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod n))))).app U).hom) := by
    apply RingHom.ext
    intro a
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective a.down
    have ha : a = (z : ULift.{u + 1} (ZMod n)) := ULift.ext hz.symm
    rw [ha]
    simp only [map_intCast]
  let c := sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} (ZMod n)))
  have hc := constantRingAb_unit X
    (CommRingCat.of (ULift.{u + 1} (ZMod n))) U a
  have hi : c.inv.hom.app U
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).app U a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod n))))).app U a := by
    rw [← hc]
    exact ((sheafToPresheaf _ _).mapIso c).hom_inv_id_app_apply U _
  change g.hom.app U (c.inv.hom.app U _) = h.hom.app U (c.inv.hom.app U _)
  exact (congrArg (g.hom.app U) hi).trans
    ((RingHom.congr_fun he a).trans (congrArg (h.hom.app U) hi).symm)

private theorem scalar_reduction (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}
    (e : CompletedRealization l X) (U : X.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U)
    (n : ℕ) :
    (purZlReduction l X (n + 1)).hom.hom.app U
        (completedRealizationScalarSection e U a) =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app U
          ((Scheme.purTwistZlProjection X l n).hom.app U a) := by
  exact congrArg (fun q ↦ q.hom.app U a) (eq_of_heq (e.unit_normalization n))

private theorem completed_push_projection (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U)
    (n : ℕ) :
    (Scheme.purTwistZlProjection X l n).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U) (completedPushScalar f U a) =
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U
          ((Scheme.purTwistZlProjection S l n).hom.app U a) := by
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  have hh : diagonalCompletedCoefficientMap l f ≫ Scheme.purTwistZlProjection X l n =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.purTwistZlProjection S l n) ≫
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) := by
    exact limit.lift_π _ (op n)
  have hc := congrArg (adj.homEquiv _ _) hh
  rw [adj.homEquiv_naturality_right, adj.homEquiv_naturality_left] at hc
  have hd : (adj.homEquiv _ _)
      (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) :=
    (adj.homEquiv _ _).apply_symm_apply _
  rw [hd] at hc
  have h := congrArg (fun q ↦ q.hom.app U a) hc
  change (Scheme.purTwistZlProjection X l n).hom.app _ (_ * 1) = _
  rw [mul_one]
  exact h

private theorem reduction_sections_ext (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ)
    (x y : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U)
    (h : ∀ n : ℕ, (purZlReduction l X (n + 1)).hom.hom.app U x =
      (purZlReduction l X (n + 1)).hom.hom.app U y) : x = y := by
  obtain ⟨e, he, _⟩ := completedCoefficientRingComparison_existsUnique l X
  have hp (n : ℕ)
      (z : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X).obj.obj U) :
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app U
          ((Scheme.purTwistZlProjection X l n).hom.app U (e.hom.hom.app U z)) =
        (purZlReduction l X (n + 1)).hom.hom.app U z := by
    have hz := congrArg (fun q ↦ q.hom.app U (e.hom.hom.app U z)) (he n)
    change (purZlReduction l X (n + 1)).hom.hom.app U
        (e.inv.hom.app U (e.hom.hom.app U z)) = _ at hz
    exact hz.symm.trans (congrArg ((purZlReduction l X (n + 1)).hom.hom.app U)
      (((sheafToPresheaf _ _).mapIso e).hom_inv_id_app_apply U z))
  apply (ConcreteCategory.bijective_of_isIso (e.hom.hom.app U)).injective
  let V := sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ CommRingCat.{u + 1}).obj U ⋙ forget CommRingCat.{u + 1}
  have hc := isLimitOfPreserves V (limit.isLimit (Scheme.purTwistZlTower X l))
  apply (Types.isLimitEquivSections hc).injective
  apply Subtype.ext
  funext n
  change (Scheme.purTwistZlProjection X l n.unop).hom.app U (e.hom.hom.app U x) =
    (Scheme.purTwistZlProjection X l n.unop).hom.app U (e.hom.hom.app U y)
  apply (ConcreteCategory.bijective_of_isIso ((sfbConstantRingAbIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))))).hom.hom.app U)).injective
  rw [hp, hp]
  exact h n.unop

private local instance constantPresheafAbBraided
    {C : Type (u + 1)} [Category.{u} C] :
    (Functor.const C : Ab.{u + 1} ⥤ C ⥤ Ab.{u + 1}).Braided where
  braided M N := by
    apply NatTrans.ext
    funext V
    change (𝟙 (M ⊗ N)) ≫ (β_ M N).hom = (β_ M N).hom ≫ (𝟙 (N ⊗ M))
    simp only [Category.id_comp, Category.comp_id]

private local instance constantAbBraided (Z : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).Braided :=
  inferInstanceAs (Functor.const Z.ProEtᵒᵖ ⋙
    presheafToSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).Braided

/-- The existing constant-section ring construction with coefficient universe independent
of the scheme universe. Its data is the sheafification of the prescribed ring map. -/
private def finiteConstantPresheafRingMap (n : ℕ) (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ R) [IsMonHom ψ] :
    (Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (ZMod n))) ⟶
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) R).obj := by
  let J := Scheme.ProEt.topology T
  let B := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let P := (Functor.const T.ProEtᵒᵖ).obj B
  let eta := toSheafify J P
  letI : MonObj P := (Functor.const T.ProEtᵒᵖ).monObjObj B
  letI : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  letI : MonObj ((constantSheaf J Ab.{u + 1}).obj B).obj :=
    (sheafToPresheaf J Ab.{u + 1}).monObjObj ((constantSheaf J Ab.{u + 1}).obj B)
  have hη : @IsMonHom _ _ _ _ _
      ((Functor.const T.ProEtᵒᵖ).monObjObj B)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj B)) eta := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have hm := Functor.monObjObj_comp (Functor.const T.ProEtᵒᵖ)
      (presheafToSheaf J Ab.{u + 1}) B
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl
      (congrArg (fun m ↦ @Functor.monObjObj _ _ _ _ _ _
        (sheafToPresheaf J Ab.{u + 1}) _ _ m) hm).symm h
  let := hη
  have hψ : @IsMonHom _ _ _ _ _
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) ψ.hom :=
    inferInstanceAs (IsMonHom ((sheafToPresheaf J Ab.{u + 1}).map ψ))
  let := hψ
  let φ := eta ≫ ψ.hom
  have hφ : @IsMonHom _ _ _ _ _ ((Functor.const T.ProEtᵒᵖ).monObjObj B)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) φ :=
    @CategoryTheory.instIsMonHomComp _ _ _ _ _ _
      ((Functor.const T.ProEtᵒᵖ).monObjObj B)
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj
        ((constantSheaf J Ab.{u + 1}).obj B))
      ((sheafToPresheaf J Ab.{u + 1}).monObjObj R) eta ψ.hom hη hψ
  exact @AdmissibleScalarRealization.constantSectionRingMapAux _ _ J
    inferInstance inferInstance inferInstance (ULift.{u + 1} (ZMod n)) inferInstance
    R inferInstance inferInstance φ hφ

private def finiteConstantRingMap (n : ℕ) (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ R) [IsMonHom ψ] :
    (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod n))) ⟶
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology T) R :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ _).symm (finiteConstantPresheafRingMap n T R ψ)

private theorem finiteConstantRingMap_normalization (n : ℕ) (T : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ R) [IsMonHom ψ]
    (U : T.ProEtᵒᵖ) (a : ULift.{u + 1} (ZMod n)) :
    (finiteConstantRingMap n T R ψ).hom.app U
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (ZMod n))))).app U a) =
    ψ.hom.app U ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).app U a) := by
  have h := ((sheafificationAdjunction (Scheme.ProEt.topology T) CommRingCat.{u + 1}).homEquiv
    _ (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) R)).apply_symm_apply
      (finiteConstantPresheafRingMap n T R ψ)
  change _ = (finiteConstantPresheafRingMap n T R ψ).app U a
  exact ConcreteCategory.congr_hom (congr_app h U) a

attribute [local irreducible] finiteConstantRingMap

private theorem constant_section_ring_map_ab (Z : Scheme.{u}) (n : ℕ)
    (R : Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (ψ : (constantSheaf (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) ⟶ R) [IsMonHom ψ] :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (finiteConstantRingMap n Z R ψ)) =
      (sfbConstantRingAbIso Z
        (CommRingCat.of (ULift.{u + 1} (ZMod n)))).hom ≫ ψ := by
  let c := sfbConstantRingAbIso Z (CommRingCat.of (ULift.{u + 1} (ZMod n)))
  apply (cancel_epi c.inv).mp
  change c.inv ≫ _ = c.inv ≫ c.hom ≫ ψ
  rw [Iso.inv_hom_id_assoc]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology Z) _ _ R.property
  ext U a
  have hc := constantRingAb_unit Z
    (CommRingCat.of (ULift.{u + 1} (ZMod n))) U a
  have hi : c.inv.hom.app U
      ((toSheafify (Scheme.ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))).app U a) =
      (toSheafify (Scheme.ProEt.topology Z)
        ((Functor.const Z.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod n))))).app U a := by
    rw [← hc]
    exact ((sheafToPresheaf _ _).mapIso c).hom_inv_id_app_apply U _
  exact (congrArg
    ((finiteConstantRingMap n Z R ψ).hom.app U) hi).trans
      (finiteConstantRingMap_normalization n Z R ψ U a)

private theorem cyclic_push_unique (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    (ψ : ((sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).X ⟶
      (lowerStar Ab.{u + 1} f).obj
        ((sfbConstantRing X).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).X)
    [IsMonHom ψ] (U : S.ProEtᵒᵖ)
    (x : ((sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).X.obj.obj U) :
    ψ.hom.app U x =
      (sfbConstantRingAbIso X (CommRingCat.of (ULift.{u + 1} (ZMod n)))).hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod n)))).hom.app U
            ((sfbConstantRingAbIso S
              (CommRingCat.of (ULift.{u + 1} (ZMod n)))).inv.hom.app U x)) := by
  let A := CommRingCat.of (ULift.{u + 1} (ZMod n))
  let CS := (sfbConstantRing S).obj ((forget₂ CommRingCat RingCat).obj A)
  let CX := (sfbConstantRing X).obj ((forget₂ CommRingCat RingCat).obj A)
  let : IsCommMonObj CS.X := by
    change IsCommMonObj ((constantSheaf (Scheme.ProEt.topology S) Ab.{u + 1}).obj
      (AddCommGrpCat.of A))
    infer_instance
  let : IsCommMonObj CX.X := by
    change IsCommMonObj ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of A))
    infer_instance
  let H := Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}
  obtain ⟨φ, hφ, _⟩ := InternalModuleOperations.sectionRingMap_existsUnique
    (Scheme.ProEt.topology S) (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
    CX.X CS.X ψ
  let cS := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (finiteConstantRingMap n S CS.X (𝟙 _))
  let cX := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (finiteConstantRingMap n X CX.X (𝟙 _))
  let d := (sheafCompose (Scheme.ProEt.topology S)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A)
  have hg : cS ≫ φ = d ≫ H.map cX := constant_cyclic_ext S n _ _
  have hs : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map cS =
      (sfbConstantRingAbIso S A).hom := by
    simpa only [Category.comp_id] using constant_section_ring_map_ab S n CS.X (𝟙 _)
  have hx : (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map cX =
      (sfbConstantRingAbIso X A).hom := by
    simpa only [Category.comp_id] using constant_section_ring_map_ab X n CX.X (𝟙 _)
  have hS : cS.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x) = x :=
    (congrArg (fun q ↦ q.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x)) hs).trans
      (((sheafToPresheaf _ _).mapIso (sfbConstantRingAbIso S A)).inv_hom_id_app_apply U x)
  calc
    ψ.hom.app U x = φ.hom.app U x := (hφ U x).symm
    _ = φ.hom.app U (cS.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x)) :=
      congrArg (φ.hom.app U) hS.symm
    _ = cX.hom.app _ (d.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x)) :=
      congrArg (fun q ↦ q.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x)) hg
    _ = _ := congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj U)
      (d.hom.app U ((sfbConstantRingAbIso S A).inv.hom.app U x))) hx

private theorem conjugate_square
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {RS QS CS : D} {RX QX CX : C}
    (aS : RS ⟶ QS) (aX : RX ⟶ QX) (b : RS ⟶ H.obj RX) (d : QS ⟶ H.obj QX)
    (kS : QS ≅ CS) (kX : QX ≅ CX) (rS : RS ⟶ CS) (rX : RX ⟶ CX)
    (hn : b ≫ H.map aX = aS ≫ d)
    (hS : aS ≫ kS.hom = rS) (hX : aX ≫ kX.hom = rX) :
    b ≫ H.map rX = rS ≫ (kS.inv ≫ d ≫ H.map kX.hom) := by
  rw [← hX, ← hS, H.map_comp, ← Category.assoc, hn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem transported_push_isMonHom
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (Q : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (kS : coefficientRing S Q ≅
      (sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
    (kX : coefficientRing X Q ≅
      (sfbConstantRing X).obj (RingCat.of (ULift.{u + 1} (ZMod n)))) :
    IsMonHom (kS.inv.hom ≫ condensedPushforwardHom Q.X f ≫
      (lowerStar Ab.{u + 1} f).map kX.hom.hom) := by
  infer_instance

private theorem push_square_apply
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {A A' : Sheaf J Ab.{u + 1}} {B B' : Sheaf K Ab.{u + 1}}
    (rS : A ⟶ A') (rX : B ⟶ B')
    (b : A ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj B)
    (d : A' ⟶ (F.sheafPushforwardContinuous Ab.{u + 1} J K).obj B')
    (h : b ≫ (F.sheafPushforwardContinuous Ab.{u + 1} J K).map rX = rS ≫ d)
    (U : Cᵒᵖ) (t : A.obj.obj U) :
    rX.hom.app (F.op.obj U) (CategoryTheory.SheafModuleSection.pushScalar F b U t) =
      d.hom.app U (rS.hom.app U t) := by
  exact congrArg (fun v ↦ v.hom.app U t) h

private theorem finite_push_of_factorization
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)
    (R Q : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) (q : R ⟶ Q)
    (kS : coefficientRing S Q ≅
      (sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
    (kX : coefficientRing X Q ≅
      (sfbConstantRing X).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
    (rS : coefficientRing S R ⟶
      (sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
    (rX : coefficientRing X R ⟶
      (sfbConstantRing X).obj (RingCat.of (ULift.{u + 1} (ZMod n))))
    (hS : (upperStarFromPoint S).mapMon.map q ≫ kS.hom = rS)
    (hX : (upperStarFromPoint X).mapMon.map q ≫ kX.hom = rX)
    (U : S.ProEtᵒᵖ) (t : (condensedRingObj R.X S).obj.obj U) :
    rX.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj U)
        (CategoryTheory.SheafModuleSection.pushScalar (Scheme.proEtaleBaseChange f)
          (condensedPushforwardHom R.X f) U t) =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod n)))).hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod n)))).hom.app U
            ((sfbConstantRingAbIso S
              (CommRingCat.of (ULift.{u + 1} (ZMod n)))).inv.hom.app U
                (rS.hom.hom.app U t))) := by
  let H := lowerStar Ab.{u + 1} f
  let ψ : ((sfbConstantRing S).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).X ⟶
      H.obj ((sfbConstantRing X).obj (RingCat.of (ULift.{u + 1} (ZMod n)))).X :=
    kS.inv.hom ≫ condensedPushforwardHom Q.X f ≫ H.map kX.hom.hom
  let : IsMonHom ψ := transported_push_isMonHom f n Q kS kX
  have hn := condensedPushforwardHom_comp_map_coefficientMap q.hom f
  have he : condensedPushforwardHom R.X f ≫ H.map rX.hom = rS.hom ≫ ψ := by
    exact conjugate_square H (coefficientMap q.hom S) (coefficientMap q.hom X)
      (condensedPushforwardHom R.X f) (condensedPushforwardHom Q.X f)
      ((Mon.forget _).mapIso kS) ((Mon.forget _).mapIso kX) rS.hom rX.hom
      hn (congrArg (fun v ↦ v.hom) hS) (congrArg (fun v ↦ v.hom) hX)
  have hs := push_square_apply (Scheme.proEtaleBaseChange f) rS.hom rX.hom
    (condensedPushforwardHom R.X f) ψ he U t
  exact hs.trans (cyclic_push_unique n f ψ U _)

/-- Keep the concrete finite comparison behind its projection equation. -/
private structure FinitePushData (l : ℕ) [Fact l.Prime] (n : ℕ) where
  Q : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  q : Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l]) ⟶ Q
  k (Z : Scheme.{u}) : coefficientRing Z Q ≅
    (sfbConstantRing Z).obj (RingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))

@[irreducible] private def finitePushData (l : ℕ) [Fact l.Prime] (n : ℕ) :
    FinitePushData.{u} l n := by
  refine ⟨_, (purZlPointReduction l).app (op (n + 1)), ?_⟩
  intro Z
  exact (purZlConstantPullbackIso l Z).app (op (n + 1)) ≪≫
    (sfbConstantRing Z).mapIso ((purZlResidueTowerIso l).app (op (n + 1)))

private theorem finitePushData_factor (l : ℕ) [Fact l.Prime] (n : ℕ)
    (Z : Scheme.{u}) :
    (upperStarFromPoint Z).mapMon.map (finitePushData.{u} l n).q ≫
      ((finitePushData.{u} l n).k Z).hom = purZlReduction l Z (n + 1) := by
  unfold finitePushData
  rfl

private theorem finite_reduction_push (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.ProEtᵒᵖ) (n : ℕ)
    (t : (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) S).obj.obj U) :
    (purZlReduction l X (n + 1)).hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U) (condensedPushScalarSection f U t) =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj U)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U
            ((sfbConstantRingAbIso S
              (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).inv.hom.app U
                ((purZlReduction l S (n + 1)).hom.hom.app U t))) := by
  let d := finitePushData.{u} l n
  have hS := finitePushData_factor l n S
  have hX := finitePushData_factor l n X
  exact finite_push_of_factorization f (l ^ (n + 1))
    (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l])) d.Q d.q (d.k S) (d.k X)
    (purZlReduction l S (n + 1)) (purZlReduction l X (n + 1))
    hS hX U t

/-- The normalized regular-module comparisons intertwine the two coefficient maps.
Only coefficients occur here: the completed direct-image action is evaluated at one
on the regular module, and there is no arbitrary module or functor comparison.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), coefficient identification;
sk-prop-sfb-qlbar-colimit-x-pullback, integral comparison paragraph.
(blueprint: lem-sfb-diagonal-completed-scalar-push).

Proof: evaluate both maps at a section of the completed coefficient ring. Compose with
every finite reduction. The unit normalizations replace each realization's regular-module
comparison by the specified finite constant-ring identification. The defining completed
coefficient limit lift and its adjunction mate identify its finite projections. On the
condensed side, factor each reduction through its point coefficient ring and use naturality
of the coefficient map. The transported finite map is the canonical constant-ring map:
ring maps from a constant cyclic ring are unique, by sheafification and integer casts.
The normalized coefficient-ring comparison and the defining limit then detect equality
from all positive reductions. Evaluation of the completed action on one is exactly its
coefficient structure map, by the definition of ringed direct image. -/
theorem completedRealization_scalar_push (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (U : S.ProEtᵒᵖ)
    (a : (Scheme.purTwistRing S (Scheme.purTwistZlCompletion S l)).obj.obj U) :
    condensedPushScalarSection f U (completedRealizationScalarSection eS U a) =
      completedRealizationScalarSection eX ((Scheme.proEtaleBaseChange f).op.obj U)
        (completedPushScalar f U a) := by
  apply reduction_sections_ext l X ((Scheme.proEtaleBaseChange f).op.obj U)
  intro n
  rw [finite_reduction_push, scalar_reduction, scalar_reduction,
    completed_push_projection]
  let c := sfbConstantRingAbIso S
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  have hc := ((sheafToPresheaf _ _).mapIso c).hom_inv_id_app_apply U
    ((Scheme.purTwistZlProjection S l n).hom.app U a)
  exact congrArg (fun z ↦ (sfbConstantRingAbIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.hom.app
      ((Scheme.proEtaleBaseChange f).op.obj U)
      ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom.app U z)) hc

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
