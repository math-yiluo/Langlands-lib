/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientRingsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

import all WeilConjectures.AlgebraicGeometry.Condensed.CondensedZlReduction
import all WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsEmbeddedCompletionDiagram
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import Mathlib.CategoryTheory.Monoidal.Internal.Limits
import Mathlib.CategoryTheory.Filtered.Final

/-! # The projection-normalized completed coefficient ring comparison

Source: the integral limit comparison in lemma-comparison-completed-coefficients.
(blueprint: lem-diagonal-completed-coefficient-ring-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option cleanup.letToHave false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

open CategoryTheory.InternalAbelianSheafModule
open scoped TensorProduct

private local instance schemeCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, 0} X

private noncomputable def ringSections (X : Scheme.{u}) :
    Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⥤
      Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1} where
  obj R := by
    let P := presheafRings ((sheafToPresheaf _ Ab.{u + 1}).obj R.X)
    refine ⟨P, ?_⟩
    apply (Presheaf.isSheaf_iff_isSheaf_comp (Scheme.ProEt.topology X) P
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).2
    exact R.X.property
  map f := ⟨{
    app Z := monToRing.map
      (((Monoidal.monFunctorCategoryEquivalence _ Ab.{u + 1}).functor.map
        ((sheafToPresheaf _ Ab.{u + 1}).mapMon.map f)).app Z)
    naturality := by
      intro Z W g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.hom.naturality g) x }⟩
  map_id R := by ext Z x; rfl
  map_comp f g := by ext Z x; rfl

private theorem ringSections_map_forget (X : Scheme.{u})
    {A B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})} (f : A ⟶ B) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      ((ringSections X).map f) = f.hom := rfl

private noncomputable def ringSectionsIso (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) :
    (ringSections X).obj
        (Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R)) ≅ R := by
  let J := Scheme.ProEt.topology X
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hmon : (sheafToPresheaf J Ab.{u + 1}).monObjObj A =
      R.obj.monObjCompForget₂ := by
    apply MonObj.ext
    let : MonObj A.obj := R.obj.monObjCompForget₂
    exact Sheaf.μ_comp_map_mul A
  apply (fullyFaithfulSheafToPresheaf J RingCat.{u + 1}).preimageIso
  refine NatIso.ofComponents (fun Z ↦ ?_) (fun f ↦ ?_)
  · refine RingEquiv.toRingCatIso
      (R := ((ringSections X).obj (Mon.mk A)).obj.obj Z)
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

attribute [local irreducible] constantPresentation

private noncomputable def constantMonIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sfbConstantRing X).obj ((forget₂ CommRingCat RingCat).obj A) ≅
      Mon.mk ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))) := by
  let e := constantPresentation.{u} (Scheme.ProEt.topology X) A
  have h := IsMonHom.of_eq e.hom
    (constantSheafRingMonObj (Scheme.ProEt.topology X) A).symm rfl
    (hf := constantPresentation_mon.{u} (Scheme.ProEt.topology X) A)
  exact Mon.mkIso e h.one_hom h.mul_hom

private theorem constantMonIso_hom (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (constantMonIso X A).hom.hom = (sfbConstantRingAbIso X A).inv := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology X) _ _
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))).property
  ext V x
  have h := constantRingAb_unit X A V x
  have he := congrArg (fun f ↦ f.app V x)
    (constantPresentation_unit.{u} (Scheme.ProEt.topology X) A)
  change (constantMonIso X A).hom.hom.hom.app V _ = _ at he
  change (constantMonIso X A).hom.hom.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj (AddCommGrpCat.of A))).app V x) =
    (sfbConstantRingAbIso X A).inv.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj (AddCommGrpCat.of A))).app V x)
  exact he.trans
    (((sheafToPresheaf _ _).mapIso (sfbConstantRingAbIso X A)).hom_inv_id_app_apply V _
      |>.symm.trans (congrArg ((sfbConstantRingAbIso X A).inv.hom.app V) h))

private noncomputable def constantRingIso (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (ringSections X).obj ((sfbConstantRing X).obj ((forget₂ CommRingCat RingCat).obj A)) ≅
      (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A) :=
  (ringSections X).mapIso (constantMonIso X A) ≪≫ ringSectionsIso X _

private theorem constantRingIso_hom (X : Scheme.{u}) (A : CommRingCat.{u + 1}) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (constantRingIso X A).hom = (sfbConstantRingAbIso X A).inv := by
  change (constantMonIso X A).hom.hom ≫ 𝟙 _ = _
  rw [Category.comp_id, constantMonIso_hom]

private theorem normalizedPointCone_limit (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
      (Cone.mk (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l]))
        (purZlPointReduction l)))) := by
  obtain ⟨ρ, hρ⟩ := (sfb_completed_coefficients.{u} l).2.1
  have he : ρ = purZlPointReduction l := by
    apply NatTrans.ext
    funext n
    apply Mon.Hom.ext
    let d := (Mon.forget _).mapIso
      (sfbPointConstantRing.mapIso ((purZlResidueTowerIso l).app n)) ≪≫
        purFinitePointIso.{u} (ZMod (l ^ n.unop))
    have hn : (ρ.app n).hom ≫ d.hom =
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap (PadicInt.toZModPow n.unop)
          (PadicInt.continuous_toZModPow n.unop)) := by
      apply purPointMap_ext
      change sfbConstantToContinuous ℤ_[l] ≫ (ρ.app n).hom ≫
        (sfbPointConstantRing.map ((purZlResidueTowerIso l).hom.app n)).hom ≫
          (purFinitePointIso.{u} (ZMod (l ^ n.unop))).hom = _
      rw [← Category.assoc, hρ.1 n.unop, ← Category.assoc]
      let C := constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}
      change (C.map _ ≫ C.map _) ≫ _ = C.map _ ≫ _
      rw [← C.map_comp, purResidueComposite, purFinitePointIso_hom]
    have hp : ((purZlPointReduction l).app n).hom ≫ d.hom = _ :=
      purPointReduction_normalized l n.unop
    calc
      (ρ.app n).hom = ((ρ.app n).hom ≫ d.hom) ≫ d.inv := by simp
      _ = (((purZlPointReduction l).app n).hom ≫ d.hom) ≫ d.inv :=
        congrArg (fun f ↦ f ≫ d.inv) (hn.trans hp.symm)
      _ = ((purZlPointReduction l).app n).hom := by simp
  rw [← he]
  exact (hρ.2.1 X).1

private theorem constantRingIso_naturality (X : Scheme.{u})
    {A B : CommRingCat.{u + 1}} (f : A ⟶ B) :
    (ringSections X).map ((sfbConstantRing X).map
        ((forget₂ CommRingCat RingCat).map f)) ≫ (constantRingIso X B).hom =
      (constantRingIso X A).hom ≫
        (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map f) := by
  apply (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  simp only [Functor.map_comp, ringSections_map_forget, constantRingIso_hom]
  rw [← constantMonIso_hom, ← constantMonIso_hom]
  change (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
      (AddCommGrpCat.ofHom f.hom.toAddMonoidHom) ≫
      (constantPresentation.{u} (Scheme.ProEt.topology X) B).hom =
    (constantPresentation.{u} (Scheme.ProEt.topology X) A).hom ≫ _
  exact constantPresentation_naturality.{u} (Scheme.ProEt.topology X) f.hom

attribute [local irreducible] constantRingIso constantMonIso ringSectionsIso

private local instance ringAb_limits (X : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})) := by
  let : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1}) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) := by
    change PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf (Scheme.ProEt.topology X)
      RingCat.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget₂ RingCat.{u + 1} Ab.{u + 1}))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})

private local instance commRing_limits (X : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
  let : PreservesLimitsOfShape ℕᵒᵖ
      (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1}) := by
    change PreservesLimitsOfShape ℕᵒᵖ (sheafToPresheaf (Scheme.ProEt.topology X)
      CommRingCat.{u + 1} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1})

private noncomputable def ringSectionsLimit (X : Scheme.{u})
    {T : ℕᵒᵖ ⥤ Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})}
    (c : Cone T) (hc : IsLimit c) : IsLimit ((ringSections X).mapCone c) := by
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : ReflectsLimitsOfShape ℕᵒᵖ V :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  apply isLimitOfReflects V
  exact isLimitOfPreserves (Mon.forget _) hc

private def positiveIndex : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show Monotone (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ Nat.add_le_add_right h 1).functor.op

private local instance positiveIndex_initial : positiveIndex.Initial :=
  Functor.initial_of_exists_of_isCofiltered positiveIndex
    (fun n ↦ ⟨n, ⟨(homOfLE (Nat.le_succ n.unop)).op⟩⟩)
    (fun {_ c} _ _ ↦ ⟨c, 𝟙 _, Subsingleton.elim _ _⟩)

private noncomputable def reductionCone (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  let c := (upperStarFromPoint X).mapMon.mapCone
    (Cone.mk (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l]))
      (purZlPointReduction l))
  let α := purZlConstantPullbackIso l X ≪≫
    Functor.isoWhiskerRight (purZlResidueTowerIso l) (sfbConstantRing X)
  ((Cone.postcompose α.hom).obj c).whisker positiveIndex

private theorem reductionCone_projection (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (n : ℕᵒᵖ) : (reductionCone l X).π.app n =
      purZlReduction l X (n.unop + 1) := by
  simp only [reductionCone, Cone.postcompose, Cone.whisker, Functor.mapCone,
    Cone.functoriality, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.comp_app, Iso.trans_hom, Functor.isoWhiskerRight_hom, positiveIndex,
    purZlReduction]
  rfl

private noncomputable def reductionConeLimit (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    IsLimit (reductionCone l X) := by
  let c := (upperStarFromPoint X).mapMon.mapCone
    (Cone.mk (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[l]))
      (purZlPointReduction l))
  let α := purZlConstantPullbackIso l X ≪≫
    Functor.isoWhiskerRight (purZlResidueTowerIso l) (sfbConstantRing X)
  exact (Functor.Initial.isLimitWhiskerEquiv positiveIndex _).symm
    ((IsLimit.postcomposeHomEquiv α c).symm (normalizedPointCone_limit l X).some)

private noncomputable def finiteDiagramIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    positiveIndex ⋙ (sfbZModCoefficientTower l ⋙ sfbConstantRing X) ⋙ ringSections X ≅
        Scheme.purTwistZlTower X l ⋙
          sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  let e (n : ℕᵒᵖ) := constantRingIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n.unop + 1)))))
  refine NatIso.ofComponents e ?_
  let τ : positiveIndex ⋙ (sfbZModCoefficientTower l ⋙ sfbConstantRing X) ⋙
      ringSections X ⟶ Scheme.purTwistZlTower X l ⋙
        sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    NatTrans.ofOpSequence (fun n ↦ (e (op n)).hom) (by
      intro n
      dsimp only [Functor.comp_map, positiveIndex, Monotone.functor,
        Functor.op_map, sfbZModCoefficientTower, Scheme.purTwistZlTower,
        Scheme.purTwistZlTowerOfUniverses, Functor.ofOpSequence_map_homOfLE_succ,
        Scheme.purTwistFiniteTransitionOfUniverses, e]
      convert! constantRingIso_naturality X (CommRingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
              (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))) using 1
      all_goals simp only [Functor.ofOpSequence_map_homOfLE_succ,
        Scheme.purTwistFiniteTransitionOfUniverses]
      all_goals rfl)
  intro n m f
  exact τ.naturality f

private theorem finiteDiagramIso_inv_ab (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (n : ℕ) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        ((finiteDiagramIso l X).inv.app (op n)) =
      (sfbConstantRingAbIso X
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom := by
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let k := constantRingIso X
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  change V.map k.inv = _
  have hk : V.mapIso k = (sfbConstantRingAbIso X
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).symm := by
    apply Iso.ext
    exact constantRingIso_hom X _
  exact congrArg Iso.inv hk

attribute [local irreducible] finiteDiagramIso

/-- The reconstructed section ring of the pulled-back condensed integers agrees with
completion, with every finite reduction fixed.

Source: blueprint latest, sec-proetale-coefficients/sk-prop-sfb-qlbar-colimit-x,
integral comparison and its Q_l specialization; the finite reductions are those of
lem-pur-condensed-zl-reduction-mod-ell-power.
(blueprint: lem-diagonal-completed-coefficient-ring-comparison).

Proof: form the cone whose vertex is the pulled-back condensed integers and whose
positive projections are purZlReduction. The normalized integral comparison makes
this a limiting cone of constant finite rings. Reconstruct section rings and identify
the finite constants by sfbConstantRingAbIso. This identifies the diagram with
purTwistZlTower, whose specified limit is purTwistZlCompletion. Uniqueness of limits
gives the ring isomorphism. Its projection equations are exactly the displayed
normalization. These projections jointly distinguish maps, proving uniqueness.
The construction applies also on the empty scheme; the positive tower suffices
because the omitted exponent-zero ring is terminal. -/
theorem completedCoefficientRingComparison_existsUnique (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) :
    ∃! e : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l),
      ∀ n : ℕ,
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.inv ≫
            (purZlReduction l X (n + 1)).hom =
          (sheafCompose (Scheme.ProEt.topology X)
            (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
              ((sheafCompose (Scheme.ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
                  (Scheme.purTwistZlProjection X l n)) ≫
            (sfbConstantRingAbIso X
              (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom := by
  classical
  dsimp only [Scheme.purTwistZlCompletion]
  unfold Scheme.purTwistZlCompletionOfUniverses
  let F := ringSections X
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let G := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let c := F.mapCone (reductionCone l X)
  let hc : IsLimit c := ringSectionsLimit X _ (reductionConeLimit l X)
  let d := G.mapCone (limit.cone (Scheme.purTwistZlTower X l))
  let hd : IsLimit d := isLimitOfPreserves G (limit.isLimit (Scheme.purTwistZlTower X l))
  let β := finiteDiagramIso l X
  let e := hc.conePointsIsoOfNatIso hd β
  have he (n : ℕ) : V.map e.inv ≫ (purZlReduction l X (n + 1)).hom =
      V.map (G.map (Scheme.purTwistZlProjection X l n)) ≫
        (sfbConstantRingAbIso X
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom := by
    have h := congrArg V.map (hc.conePointsIsoOfNatIso_inv_comp hd β (op n))
    simp only [Functor.map_comp] at h
    have hb : V.map (β.inv.app (op n)) =
        (sfbConstantRingAbIso X
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom :=
      finiteDiagramIso_inv_ab l X n
    rw [hb] at h
    simpa only [c, d, F, G, V, Functor.mapCone, Cone.functoriality,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, ringSections_map_forget,
      reductionCone_projection, limit.cone_π, Scheme.purTwistZlProjection,
      Scheme.purTwistZlProjectionOfUniverses] using h
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext_inv
  apply hc.hom_ext
  intro n
  apply V.map_injective
  simp only [Functor.map_comp, c, F, V, Functor.mapCone, Cone.functoriality,
    ringSections_map_forget, reductionCone_projection]
  exact (he' n.unop).trans (he n.unop).symm

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
