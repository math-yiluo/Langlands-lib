/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralContinuousPresentationMatrix
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import all WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-!
# Compatibility of scalar cokernel classes on presentation covers

Source: HRS Example 3.1 and the geometric evaluation argument in the parent node.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₁ w₁
open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Profinite.continuousMapRingObjOfUniverseMonObj
attribute [local instance] Profinite.isCommMonObj_continuousMapRingObjOfUniverse
namespace AlgebraicGeometry.ProEtale.ContinuousRingUniverse

private instance canonicalComparisonIsIso (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) : IsIso (comparison X E) := comparison_isIso X E

private noncomputable def continuousCoefficientValue (E : Type u)
    [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (X : Scheme.{u})
    (g : coeff E X ⟶ coeff E X) := coeffEndFun g

/-- Continuous coefficient of a regular endomorphism at a geometric point. -/
@[irreducible] private noncomputable def condensedFieldPointCoefficient
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (f : Mod.regular
        (condensedRingObj (baseRing E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (baseRing E) (Spec (.of Ω)))) : E :=
  ((((inv (comparison (Spec (.of Ω)) E)) ≫ f.hom ≫
    (comparison (Spec (.of Ω)) E)).hom.app
      (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))) (ULift.up 1)).down z

/-- The regular-module normalization of evaluation over a geometric point. -/
private def CondensedFieldPointScalarProperty
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
      (condensedRingObj (baseRing E) (Spec (.of Ω))) ⥤
      ModuleCat.{u + 1} E) : Prop :=
  ∃ b : H.obj (Mod.regular
      (condensedRingObj (baseRing E) (Spec (.of Ω)))) ≃ₗ[E] E,
    ∀ f : Mod.regular
        (condensedRingObj (baseRing E) (Spec (.of Ω))) ⟶
        Mod.regular
          (condensedRingObj (baseRing E) (Spec (.of Ω))),
      b (H.map f (b.symm 1)) =
        condensedFieldPointCoefficient E Ω z f

-- The upstream Functor.Monoidal.evaluation has these same identity comparisons, but its
-- GlobalSectionsMonoidal module conflicts with the finite-coefficient notation imports here.
private noncomputable instance evaluationMonoidal
    {C : Type*} [Category C] {D : Type*} [Category D] [MonoidalCategory D] (U : C) :
    ((evaluation C D).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

private noncomputable abbrev pointSections (Ω : Type u) [Field Ω] :=
  sheafToPresheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))

private noncomputable def pointConstants
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    ULift.{u + 1} E ≃+* ULift.{u + 1} C(Spec (.of Ω), E) where
  toFun x := ULift.up (ContinuousMap.const _ x.down)
  invFun f := ULift.up (f.down z)
  left_inv _ := rfl
  right_inv f := by
    apply ULift.ext
    ext y
    exact congrArg f.down (Subsingleton.elim z y)
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private lemma pointSectionsMonObj
    (Ω : Type u) [Field Ω]
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) RingCat.{u + 1}) :
    (pointSections Ω).monObjObj
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R) =
      AddCommGrpCat.ringMonObj
        (R.obj.obj (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))) := by
  apply MonObj.ext
  let : MonObj ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R).obj :=
      R.obj.monObjCompForget₂
  have h := congr_app (Sheaf.μ_comp_map_mul
    ((sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R))
        (Opposite.op (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))
  change (𝟙 _ ≫ _) ≫ _ = _
  rw [Category.id_comp]
  exact h

private noncomputable abbrev pointContinuousObj
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (Ω : Type u) [Field Ω] :=
  (sheafCompose (Scheme.ProEt.topology (Spec (.of Ω)))
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf (Spec (.of Ω)) E)

private noncomputable def pointConstantHom
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    AddCommGrpCat.of (ULift.{u + 1} E) ⟶ (pointSections Ω).obj (pointContinuousObj E Ω) :=
  (pointConstants E Ω z).toAddEquiv.toAddCommGrpIso.hom

private instance pointConstantHom_isMonHom
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsMonHom (pointConstantHom E Ω z) := by
  have h := pointSectionsMonObj Ω (continuousCoefficientRingSheaf (Spec (.of Ω)) E)
  change @IsMonHom _ _ _ _ _ _ ((pointSections Ω).monObjObj _) _
  rw [h]
  exact AddCommGrpCat.isMonHom_ofHom_ringHom (pointConstants E Ω z).toRingHom

private instance pointConstantHom_isIso
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsIso (pointConstantHom E Ω z) := by
  unfold pointConstantHom
  infer_instance

private noncomputable def pointScalarHom
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    AddCommGrpCat.of (ULift.{u + 1} E) ⟶ (pointSections Ω).obj
      (condensedRingObj (baseRing E) (Spec (.of Ω))) :=
  pointConstantHom E Ω z ≫ (pointSections Ω).map
    (inv (comparison (Spec (.of Ω)) E))

private instance pointScalarHom_isMonHom
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsMonHom (pointScalarHom E Ω z) := by
  unfold pointScalarHom
  infer_instance

private instance pointScalarHom_isIso
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    IsIso (pointScalarHom E Ω z) := by
  unfold pointScalarHom
  infer_instance

private noncomputable abbrev pointInternalEvaluation
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :=
  (pointSections Ω).mapMod
      (condensedRingObj (baseRing E) (Spec (.of Ω))) ⋙
    Mod.comap (pointScalarHom E Ω z)

private noncomputable def pointEvaluation
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :=
  pointInternalEvaluation E Ω z ⋙ CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom

private instance pointEvaluation_additive
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointEvaluation E Ω z).Additive := by
  have : (CategoryTheory.internalToModule (ULift.{u + 1} E)).Additive :=
    ⟨by intros; rfl⟩
  unfold pointEvaluation
  infer_instance

private instance pointEvaluation_preservesFiniteColimits
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω)) :
    PreservesFiniteColimits (pointEvaluation E Ω z) := by
  have : PreservesFiniteColimits (pointSections Ω) :=
    (geometric_field_proetale_evaluation_exact Ω).2.2.1
  unfold pointEvaluation
  infer_instance

private noncomputable def pointRegularIso
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointInternalEvaluation E Ω z).obj
        (Mod.regular
          (condensedRingObj (baseRing E) (Spec (.of Ω)))) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} E)) := by
  let r := pointScalarHom E Ω z
  refine Mod.isoMk (asIso r).symm ?_
  change (r ▷ _ ≫ MonObj.mul) ≫ inv r = _ ◁ inv r ≫ MonObj.mul
  rw [Category.assoc, IsMonHom.mul_hom, MonoidalCategory.tensorHom_def, Category.assoc,
    ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight, Category.id_comp]

private noncomputable def liftedRegularCoordinates (E : Type u) [Ring E] :
    ((CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
        ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom).obj
      (Mod.regular (AddCommGrpCat.of (ULift.{u + 1} E)))) ≃ₗ[E] E where
  toFun x := x.down
  invFun x := ULift.up x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def pointCoordinates
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) :
    (pointEvaluation E Ω z).obj
        (Mod.regular
          (condensedRingObj (baseRing E)
            (Spec (.of Ω)))) ≃ₗ[E] E := by
  let G := CategoryTheory.internalToModule (ULift.{u + 1} E) ⋙
    ModuleCat.restrictScalars ULift.ringEquiv.symm.toRingHom
  exact (G.mapIso (pointRegularIso E Ω z)).toLinearEquiv.trans (liftedRegularCoordinates E)

/-- Evaluation at the final object over one algebraically closed field.

Source: Bhatt--Scholze, Example 4.2.11; Hemo--Richarz--Scholbach, Example 3.1
(auxiliary; not a blueprint node).

Proof in words. Apply final-object sections to the underlying abelian sheaf and its
internal action. Sections is lax monoidal: its tensorator sends a pair of sections to
its tensor section, so its image is an internal module over the ring of global sections.
The canonical continuous realization identifies this ring with ULift E: every continuous
function on the one-point spectrum is constant, and evaluation at z is its inverse.
Transport the action along this ring isomorphism and use the tensor universal property
for internal modules in abelian groups to obtain an ordinary E-module. The internal
linearity diagrams make all evaluated arrows E-linear; they are unchanged as additive
maps, hence this functor is additive. Over an algebraically closed field every covering
of the final object splits. Consequently abelian sections preserves finite colimits.
The forgetful functor from internal modules computes those colimits, and the ordinary
module forgetful functor reflects them; hence evaluation preserves finite colimits.
The regular module gives E with its usual action. Evaluate its endomorphism at 1 to
get the displayed normalization, since both coefficient identifications are the
specified continuous realization followed by evaluation at z. -/
private theorem exists_condensedField_point_evaluation
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω)) :
    ∃ H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
        (condensedRingObj (baseRing E) (Spec (.of Ω))) ⥤
        ModuleCat.{u + 1} E,
      H.Additive ∧ PreservesFiniteColimits H ∧ CondensedFieldPointScalarProperty E Ω z H := by
  refine ⟨pointEvaluation E Ω z, inferInstance, inferInstance, pointCoordinates E Ω z, ?_⟩
  intro f
  change (inv (pointScalarHom E Ω z)
    (((pointSections Ω).map f.hom) ((pointScalarHom E Ω z) (ULift.up 1)))).down = _
  unfold pointScalarHom
  rw [IsIso.inv_comp, ← Functor.map_inv]
  have he : inv (inv (comparison (Spec (.of Ω)) E)) =
      comparison (Spec (.of Ω)) E := IsIso.inv_inv
  have hc : inv (pointConstantHom E Ω z) =
      AddCommGrpCat.ofHom (pointConstants E Ω z).symm.toAddMonoidHom := by
    apply IsIso.inv_eq_of_hom_inv_id
    ext a
    rfl
  rw [he, hc]
  unfold condensedFieldPointCoefficient
  rfl

-- Keep scalar evaluation folded while composing identities: reducing the concrete
-- realization and pullback morphisms here expands their underlying constructions.
@[irreducible] private noncomputable def coefficientValue
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (X : Scheme.{u}) (x : X)
    (g : coeff E X ⟶ coeff E X) : E :=
  coeffEndFun g x

@[irreducible] private noncomputable def ringScalar
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (X : Scheme.{u}) (x : X)
    (g : condensedRingObj (baseRing E) X ⟶
      condensedRingObj (baseRing E) X) : E :=
  coefficientValue E X x ((inv (comparison X E)) ≫ g ≫
    (comparison X E))

private noncomputable def continuousPush (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    {T V : Scheme.{u}} (a : T ⟶ V) :
    coeff E V ⟶ (lowerStar AddCommGrpCat.{u + 1} a).obj (coeff E T) :=
  ⟨{ app := fun U ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ ULift.up
            (s.down.comp (pullback.fst U.unop.hom a).base.hom)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro U W f
       apply ConcreteCategory.hom_ext
       intro s
       apply ULift.ext
       ext x
       have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ a).map f.unop).left ≫
           pullback.fst U.unop.hom a = pullback.fst W.unop.hom a ≫ f.unop.left := by
         simp [MorphismProperty.Over.pullback]
       exact congrArg s.down (congrArg (fun g : pullback W.unop.hom a ⟶ U.unop.left ↦
         g x) h.symm) }⟩

private lemma realization_adjoint (E : Type u)
    [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E]
    [TotallyDisconnectedSpace E] (X : Scheme.{u}) :
    ((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _)
        (comparison X E) = comparisonAdjoint X E := by
  unfold comparison
  exact Equiv.apply_symm_apply _ _

private theorem realization_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E] :
    condensedPushforwardHom (baseRing E) f ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (comparison Y E) =
    (comparison X E) ≫ continuousPush E f := by
  let adjX := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  have hleft := CondensedRing.chartMate_homEquiv f (toSpecZ X) (toSpecZ Y)
    (comp_toSpecZ f) (pointUpperStar.obj (baseRing E))
    (coeff E Y) (comparison Y E)
  rw [← condensedPullbackHom_eq (baseRing E) f] at hleft
  apply (adjX.homEquiv _ _).injective
  conv_rhs => rw [adjX.homEquiv_naturality_right]
  rw [show adjX.homEquiv _ _ (comparison X E) =
    comparisonAdjoint X E from realization_adjoint E X]
  simp only [adjX, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [condensedPushforwardHom, Adjunction.unitAlgHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  have hY := realization_adjoint E Y
  simp only [Adjunction.comp_homEquiv] at hY
  erw [hY]
  ext S s
  apply ULift.ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  change ((((lowerStarFactor AddCommGrpCat.{u + 1} (comp_toSpecZ f)).inv.app
    (coeff E Y)).hom.app (op (profiniteToProEt.obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection Y S.unop)))).down =
    (((continuousPush E f).hom.app (op ((profiniteToProEtOf X).obj S.unop)))
      (ULift.up (s.down.comp (profiniteTestProjection X S.unop)))).down
  rw [lowerStarFactor_inv_app_hom_app]
  change (s.down.comp (profiniteTestProjection Y S.unop)).comp
      (((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left.base.hom) =
    (s.down.comp (profiniteTestProjection X S.unop)).comp
      (pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f).base.hom
  have hp :
      ((MorphismProperty.Over.pullbackComp f (toSpecZ X) (toSpecZ Y)
        (comp_toSpecZ f).symm).inv.app (profiniteToProEt.obj S.unop)).left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) =
      pullback.fst (((profiniteToProEtOf X).obj S.unop).hom) f ≫
        pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ X) := by
    simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
    dsimp only [pullback.map]
    erw [Category.assoc, pullback.lift_fst]
    simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
    rfl
  have hp' := congrArg (fun g ↦ g.base.hom) hp
  simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
  simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
  rw [hp']

private theorem continuous_unit_scalar {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (p : coeff E X ⟶ coeff E X)
    (q : coeff E Y ⟶ coeff E Y)
    (h : continuousPush E f ≫ (lowerStar AddCommGrpCat.{u + 1} f).map q =
      p ≫ continuousPush E f) (y : Y) :
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (f y) := by
  let V : Y.ProEt := Scheme.ProEt.mk (pullback.snd (𝟙 X) f)
  let v : V ⟶ Scheme.ProEt.mk (𝟙 Y) := MorphismProperty.Over.homMk V.hom
  let w : Y ⟶ pullback (𝟙 X) f := pullback.lift f (𝟙 Y) (by simp)
  let z := w y
  have hs := congrArg (fun k ↦ ((k.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    (ULift.up 1)).down z) h
  have hn := congrArg (fun k : AddCommGrpCat.of (ULift.{u + 1} C(Y, E)) ⟶
      AddCommGrpCat.of (ULift.{u + 1} C(V.left, E)) ↦ (k (ULift.up 1)).down z)
    (q.hom.naturality v.op)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    lowerStar_map_hom_app, AddCommGrpCat.comp_apply] at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down
      (pullback.fst (𝟙 X) f z) at hs
  change ((q.hom.app (op V)) (ULift.up 1)).down z =
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down (V.hom z) at hn
  have hw₁ : w ≫ pullback.fst (𝟙 X) f = f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ V.hom = 𝟙 Y := pullback.lift_snd _ _ _
  have hz₁ : pullback.fst (𝟙 X) f z = f y :=
    congrArg (fun h : Y ⟶ X ↦ h y) hw₁
  have hz₂ : V.hom z = y := congrArg (fun h : Y ⟶ Y ↦ h y) hw₂
  rw [hz₁] at hs
  rw [hz₂] at hn
  exact hn.symm.trans hs

private theorem continuous_unit_scalar_value {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] (p : coeff E X ⟶ coeff E X)
    (q : coeff E Y ⟶ coeff E Y)
    (h : continuousPush E f ≫ (lowerStar AddCommGrpCat.{u + 1} f).map q =
      p ≫ continuousPush E f) (y : Y) :
    coefficientValue E Y y q = coefficientValue E X (f y) p := by
  delta coefficientValue continuousCoefficientValue coeffEndFun
  exact continuous_unit_scalar f E p q h y

private theorem adjunction_conjugation
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A : C} {B : D} (α : L.obj A ⟶ B) [IsIso α] (p : A ⟶ A) :
    p ≫ (adj.unit.app A ≫ R.map α) =
      (adj.unit.app A ≫ R.map α) ≫ R.map (inv α ≫ L.map p ≫ α) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc, IsIso.hom_inv_id, R.map_id, Category.id_comp]
  simpa only [Functor.id_map, Functor.id_obj, Functor.comp_map, Category.assoc] using
    congrArg (fun h ↦ h ≫ R.map α) (adj.unit.naturality p)

private theorem scalar_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (p : condensedRingObj (baseRing E) X ⟶
      condensedRingObj (baseRing E) X) (y : Y) :
    ringScalar E Y y
      (inv (condensedPullbackHom (baseRing E) f) ≫
        (upperStar AddCommGrpCat.{u + 1} f).map p ≫
          condensedPullbackHom (baseRing E) f) =
      ringScalar E X (f y) p := by
  delta ringScalar
  apply continuous_unit_scalar_value f E
  have h := CondensedRing.conjugated_morphism_square
    (lowerStar AddCommGrpCat.{u + 1} f)
    (comparison X E)
    (comparison Y E)
    (condensedPushforwardHom (baseRing E) f)
    (continuousPush E f) p _ (realization_naturality f E)
    (adjunction_conjugation (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
      (condensedPullbackHom (baseRing E) f) p)
  exact h

private lemma conjugate_factor
    {C : Type*} [Category C] {A B D : C}
    (α : A ⟶ B) [IsIso α] (β : B ⟶ D) [IsIso β]
    (γ : A ⟶ D) [IsIso γ] (hγ : γ = α ≫ β) (f : A ⟶ A) :
    inv γ ≫ f ≫ γ = inv β ≫ (inv α ≫ f ≫ α) ≫ β := by
  subst γ
  simp only [IsIso.inv_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency.types true in
private lemma realization_conjugate
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (p : V ⟶ X)
    (f : (upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (baseRing E) X) ⟶
      (upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (baseRing E) X)) :
    inv (pullbackComparison E p) ≫ f ≫
        pullbackComparison E p =
      (inv (comparison V E)) ≫
        (inv (coefficientComparison E p) ≫ f ≫
          coefficientComparison E p) ≫
        (comparison V E) := by
  exact conjugate_factor (coefficientComparison E p) (comparison V E)
    (pullbackComparison E p) (pullbackComparison_eq E p) f

private lemma pointCoefficient_eq
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω))
    (g : Mod.regular
      (condensedRingObj (baseRing E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (baseRing E) (Spec (.of Ω)))) :
    condensedFieldPointCoefficient E Ω z g = ringScalar E (Spec (.of Ω)) z g.hom := by
  delta condensedFieldPointCoefficient ringScalar coefficientValue
    continuousCoefficientValue coeffEndFun
  rfl

private lemma pointCoefficient_from_hom
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] (z : Spec (.of Ω)) {V : Scheme.{u}}
    (a : Spec (.of Ω) ⟶ V)
    (p : condensedRingObj (baseRing E) V ⟶
      condensedRingObj (baseRing E) V)
    (g : Mod.regular
      (condensedRingObj (baseRing E) (Spec (.of Ω))) ⟶
      Mod.regular
        (condensedRingObj (baseRing E) (Spec (.of Ω))))
    (h : g.hom = inv (condensedPullbackHom (baseRing E) a) ≫
      (upperStar AddCommGrpCat.{u + 1} a).map p ≫
        condensedPullbackHom (baseRing E) a) :
    condensedFieldPointCoefficient E Ω z g = ringScalar E V (a z) p := by
  have hg := congrArg (ringScalar E (Spec (.of Ω)) z) h
  exact (pointCoefficient_eq E Ω z g).trans (hg.trans (scalar_naturality a E p z))

private lemma pullbackScalar_eq
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    {X V : Scheme.{u}} (p : V ⟶ X) (x : V)
    (f : (upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (baseRing E) X) ⟶
      (upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (baseRing E) X)) :
    coefficientValue E V x (inv (pullbackComparison E p) ≫ f ≫
      pullbackComparison E p) =
      ringScalar E V x
        (inv (condensedPullbackHom (baseRing E) p) ≫ f ≫
          condensedPullbackHom (baseRing E) p) := by
  delta ringScalar
  simpa only [coefficientComparison_eq] using
    congrArg (coefficientValue E V x) (realization_conjugate E p f)

private lemma geometric_scalar_value
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (Ω : Type u) [Field Ω] {X V : Scheme.{u}}
    (p : V ⟶ X) (a : Spec (.of Ω) ⟶ V) (z : Spec (.of Ω))
    (f : Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (baseRing E) X)) ⟶
      Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
        (condensedRingObj (baseRing E) X))) :
    condensedFieldPointCoefficient E Ω z
      ((condensedFieldGeometricRegularIso (baseRing E) p a).inv ≫
        (condensedFieldGeometricModulePullback
          (baseRing E) p a).map f ≫
        (condensedFieldGeometricRegularIso (baseRing E) p a).hom) =
      coefficientValue E V (a z)
        (inv (pullbackComparison E p) ≫ f.hom ≫
          pullbackComparison E p) := by
  have h := pointCoefficient_from_hom E Ω z a
    (inv (condensedPullbackHom (baseRing E) p) ≫ f.hom ≫
      condensedPullbackHom (baseRing E) p)
    ((condensedFieldGeometricRegularIso (baseRing E) p a).inv ≫
      (condensedFieldGeometricModulePullback (baseRing E) p a).map f ≫
      (condensedFieldGeometricRegularIso (baseRing E) p a).hom)
    (AlgebraicGeometry.ProEtale.regular_conjugate (baseRing E) p a f)
  exact h.trans (pullbackScalar_eq E p (a z) f.hom).symm

@[irreducible] private noncomputable def transportedCoordinates
    {C : Type*} [Category C] {E : Type u} [CommRing E]
    (H : C ⥤ ModuleCat.{u + 1} E) {A B : C} (t : A ≅ B)
    (b₀ : H.obj B ≃ₗ[E] E) : H.obj A ≃ₗ[E] E :=
  (H.mapIso t).toLinearEquiv.trans b₀

private lemma conjugatedScalar
    {C : Type*} [Category C] {E : Type u} [CommRing E]
    (H : C ⥤ ModuleCat.{u + 1} E) {A B : C} (t : A ≅ B)
    (b₀ : H.obj B ≃ₗ[E] E) (f : A ⟶ A) :
    transportedCoordinates H t b₀
        (H.map f ((transportedCoordinates H t b₀).symm 1)) =
      b₀ (H.map (t.inv ≫ f ≫ t.hom) (b₀.symm 1)) := by
  unfold transportedCoordinates
  change b₀ ((H.map t.hom) ((H.map f) ((H.map t.inv) (b₀.symm 1)))) = _
  rw [Functor.map_comp, Functor.map_comp]
  rfl

/-- Coordinate transport reduces scalar computation to conjugation. -/
private theorem condensedField_coordinates_of_conjugacy
    {C D : Type*} [Category C] [Category D] {E : Type u} [CommRing E]
    (P : C ⥤ D) (H : D ⥤ ModuleCat.{u + 1} E) (A : C) (B : D)
    (t : P.obj A ≅ B) (cB : (B ⟶ B) → E) {cA : (A ⟶ A) → E}
    (hB : ∃ b₀ : H.obj B ≃ₗ[E] E, ∀ f, b₀ (H.map f (b₀.symm 1)) = cB f)
    (hc : ∀ f, cB (t.inv ≫ P.map f ≫ t.hom) = cA f) :
    ∃ b : (P ⋙ H).obj A ≃ₗ[E] E,
      ∀ f, b ((P ⋙ H).map f (b.symm 1)) = cA f := by
  obtain ⟨b₀, hb₀⟩ := hB
  refine ⟨transportedCoordinates H t b₀, fun f ↦ ?_⟩
  exact (conjugatedScalar H t b₀ (P.map f)).trans
    ((hb₀ (t.inv ≫ P.map f ≫ t.hom)).trans (hc f))

/-- Transport the normalized regular-module evaluation along one geometric map.

Source: Hemo--Richarz--Scholbach, Example 3.1; the adjoint-test characterization of
continuous realization in `condensedFieldContinuousMapIso_test`
(auxiliary; not a blueprint node).

Proof in words. Restriction along the inverse coefficient isomorphism sends the
regular pulled-back coefficient module to the regular coefficient module on V.
The canonical isomorphism is the coefficient isomorphism itself. Module inverse image
along a sends that regular module to the regular coefficient module on Spec Ω, by the
strong monoidality of inverse image and the extension-of-scalars regular-module
comparison. Let t denote their composite. Apply H to t and compose with the given
regular-module coordinate b on Spec Ω; this gives the required linear equivalence.
Conjugation by t transports every regular-module endomorphism f. The normalization
of H computes its scalar from the canonical continuous realization on Spec Ω.
The adjoint-test equation for that realization, naturality of the unit, and the
coefficient pullback comparison identify this transported coefficient with the
pullback along a of the continuous coefficient of f on V. A continuous function
pulled back to Spec Ω has value at z equal to its original value at a(z). This proves
the formula. The argument needs no finite presentation and is valid for any H with
the stated normalization; a zero functor cannot satisfy that normalization. -/
private theorem condensedField_geometric_evaluation_scalars
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (X V : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (p : V ⟶ X) (a : Spec (.of Ω) ⟶ V) (z : Spec (.of Ω))
    (H : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) AddCommGrpCat.{u + 1})
      (condensedRingObj (baseRing E) (Spec (.of Ω))) ⥤
      ModuleCat.{u + 1} E)
    (hH : CondensedFieldPointScalarProperty E Ω z H) :
    let R := condensedRingObj (baseRing E) X
    let Ri := (upperStar AddCommGrpCat.{u + 1} p).obj R
    let F :=
      condensedFieldGeometricModulePullback (baseRing E) p a ⋙ H
    ∃ b : F.obj (Mod.regular Ri) ≃ₗ[E] E,
      ∀ f : Mod.regular Ri ⟶ Mod.regular Ri,
        b (F.map f (b.symm 1)) =
          continuousCoefficientValue E V
            (inv (pullbackComparison E p) ≫ f.hom ≫
              pullbackComparison E p) (a z) := by
  dsimp (config := { proj := false }) only
  apply condensedField_coordinates_of_conjugacy
    (condensedFieldGeometricModulePullback (baseRing E) p a)
    H (Mod.regular ((upperStar AddCommGrpCat.{u + 1} p).obj
      (condensedRingObj (baseRing E) X)))
    (Mod.regular (condensedRingObj (baseRing E) (Spec (.of Ω))))
    (condensedFieldGeometricRegularIso (baseRing E) p a)
    (condensedFieldPointCoefficient E Ω z) hH
  intro f
  simpa only [coefficientValue, continuousCoefficientValue] using geometric_scalar_value E Ω p a z f

/-- Compatible geometric evaluation, independent of any chosen module or presentation.
Source: the geometric evaluation step of the rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1; Bhatt--Scholze, Example 4.2.11
(auxiliary; not a blueprint node).

Proof: use the supplied maps from the common algebraically closed field. First
extend scalars along the canonical coefficient isomorphism for p or g, then apply
module inverse image along a or d. Both routes end in modules over the condensed
coefficient ring on Spec(Omega). Evaluate their underlying sheaves and actions at
the final object. The continuous realization identifies that ring with ULift E,
since the spectrum of a field has one point. Define the E-action on each evaluated
module by applying its internal action to ULift(e) tensor m. The tensor universal
property and internal unit and associativity equations give an ordinary E-module;
the internal linearity diagram makes every evaluated morphism E-linear.

A pro-etale cover of an algebraically closed field splits through a member, so
abelian evaluation preserves cokernels. Finite colimits of internal modules are
computed on their underlying abelian sheaves, as tensoring preserves these
colimits. The ordinary module forgetful functor reflects these colimits, proving
finite-colimit preservation of evaluation. Inverse image and change of scalars
preserve finite colimits too. Each construction is additive. The module inverse
image composition comparisons, coefficient comparisons and the equality had give
the displayed natural isomorphism on all modules over X.

The regular coefficient module evaluates to E, giving b and c by evaluation at 1.
An endomorphism of the regular module is multiplication by its value on 1. The
adjoint-test characterization of the canonical continuous realization identifies
its image under geometric pullback with the value of its continuous coefficient
at a(z) or d(z). This proves both scalar formulas. The maps from the field exclude
empty source schemes V and W. No finite presentation or finite rank is required. -/
private theorem exists_condensedField_compatible_evaluations
    (E : Type u) [CommRing E]
    [TopologicalSpace E] [IsTopologicalRing E] [TotallyDisconnectedSpace E]
    (X V W : Scheme.{u}) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (p : V ⟶ X) (g : W ⟶ X)
    (a : Spec (.of Ω) ⟶ V) (d : Spec (.of Ω) ⟶ W)
    (had : a ≫ p = d ≫ g) (z : Spec (.of Ω)) :
    let R := condensedRingObj (baseRing E) X
    let Ri := (upperStar AddCommGrpCat.{u + 1} p).obj R
    let Rj := (upperStar AddCommGrpCat.{u + 1} g).obj R
    ∃ (F : Mod (Sheaf (Scheme.ProEt.topology V) AddCommGrpCat.{u + 1}) Ri ⥤
        ModuleCat.{u + 1} E)
      (G : Mod (Sheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}) Rj ⥤
        ModuleCat.{u + 1} E),
      F.Additive ∧ G.Additive ∧ PreservesFiniteColimits F ∧ PreservesFiniteColimits G ∧
      Nonempty (((upperStar AddCommGrpCat.{u + 1} p).mapMod R) ⋙ F ≅
        ((upperStar AddCommGrpCat.{u + 1} g).mapMod R) ⋙ G) ∧
      ∃ (b : F.obj (Mod.regular Ri) ≃ₗ[E] E)
        (c : G.obj (Mod.regular Rj) ≃ₗ[E] E),
        (∀ f : Mod.regular Ri ⟶ Mod.regular Ri,
          b (F.map f (b.symm 1)) =
            continuousCoefficientValue E V
              (inv (pullbackComparison E p) ≫ f.hom ≫
                pullbackComparison E p) (a z)) ∧
        (∀ f : Mod.regular Rj ⟶ Mod.regular Rj,
          c (G.map f (c.symm 1)) =
            continuousCoefficientValue E W
              (inv (pullbackComparison E g) ≫ f.hom ≫
                pullbackComparison E g) (d z)) := by
  let Λ := baseRing E
  let R := condensedRingObj Λ X
  obtain ⟨H, hHa, hHc, hHs⟩ := exists_condensedField_point_evaluation E Ω z
  let := hHa
  let := hHc
  let P := condensedFieldGeometricModulePullback (baseRing E) p a
  let Q := condensedFieldGeometricModulePullback (baseRing E) g d
  let F := P ⋙ H
  let G := Q ⋙ H
  let e : (upperStar AddCommGrpCat.{u + 1} p).mapMod R ⋙ F ≅
      (upperStar AddCommGrpCat.{u + 1} g).mapMod R ⋙ G :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ p a) H ≪≫
      Functor.isoWhiskerRight (eqToIso (congrArg (CondensedRing.upperStar Λ) had)) H ≪≫
      (Functor.isoWhiskerRight (condensedFieldGeometricModulePullbackComp Λ g d) H).symm ≪≫
      Functor.associator _ _ _
  obtain ⟨b, hb⟩ := condensedField_geometric_evaluation_scalars E X V Ω p a z H hHs
  obtain ⟨c, hc⟩ := condensedField_geometric_evaluation_scalars E X W Ω g d z H hHs
  refine ⟨F, G, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e⟩, b, c, ?_, ?_⟩
  · exact hb
  · exact hc

section FiniteFreeCoordinates

variable {E : Type v} [CommRing E]
variable {D : Type v₁} [Category.{w₁} D] [Preadditive D] [HasFiniteBiproducts D]
variable (A : D) (F : D ⥤ ModuleCat.{w} E) [F.Additive]
variable (e : F.obj A ≃ₗ[E] E)

/-- Coordinates obtained from the biproduct comparison and the regular-module coordinates. -/
@[irreducible] private noncomputable def finiteFreeEvaluationCoords (k : ℕ) :
    F.obj (⨁ fun _ : Fin k ↦ A) ≃ₗ[E] (Fin k → E) :=
  ((F.mapBiproduct (fun _ : Fin k ↦ A)).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi (fun _ : Fin k ↦ F.obj A)).toLinearEquiv).trans
      (LinearEquiv.piCongrRight fun _ ↦ e)

private lemma finiteFreeEvaluationCoords_apply (k : ℕ) (j : Fin k)
    (x : F.obj (⨁ fun _ : Fin k ↦ A)) :
    finiteFreeEvaluationCoords A F e k x j = e ((F.map (biproduct.π (fun _ : Fin k ↦ A) j)) x) := by
  unfold finiteFreeEvaluationCoords
  change e (((ModuleCat.biproductIsoPi _).hom ≫
    ModuleCat.ofHom (LinearMap.proj j)).hom
      ((F.mapBiproduct (fun _ : Fin k ↦ A)).hom x)) = _
  congr 1
  have hp : (ModuleCat.biproductIsoPi (F.obj ∘ (fun _ : Fin k ↦ A))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π _ j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  have h := F.biproductComparison_π (fun _ : Fin k ↦ A) j
  rw [← hp] at h
  exact congrArg (fun t ↦ t x) h

private lemma finiteFreeEvaluationCoords_symm_single (k : ℕ) (j : Fin k) (x : E) :
    (finiteFreeEvaluationCoords A F e k).symm (Pi.single j x) =
      F.map (biproduct.ι (fun _ : Fin k ↦ A) j) (e.symm x) := by
  classical
  apply (finiteFreeEvaluationCoords A F e k).injective
  ext i
  rw [LinearEquiv.apply_symm_apply, finiteFreeEvaluationCoords_apply]
  change (Pi.single j x : Fin k → E) i = e ((F.map (biproduct.ι (fun _ : Fin k ↦ A) j) ≫
      F.map (biproduct.π (fun _ : Fin k ↦ A) i))
    (e.symm x))
  rw [← F.map_comp]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

private lemma finiteFreeEvaluationCoords_matrix (m n : ℕ)
    (f : (⨁ fun _ : Fin m ↦ A) ⟶ ⨁ fun _ : Fin n ↦ A)
    (M : Matrix (Fin n) (Fin m) E)
    (h : ∀ i j, e (F.map (biproduct.ι _ j ≫ f ≫ biproduct.π _ i) (e.symm 1)) =
      M i j) :
    (finiteFreeEvaluationCoords A F e n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords A F e m).symm.toLinearMap = M.mulVecLin := by
  classical
  apply LinearMap.toMatrix'.injective
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change finiteFreeEvaluationCoords A F e n
    (F.map f ((finiteFreeEvaluationCoords A F e m).symm (Pi.single j 1))) i = _
  rw [finiteFreeEvaluationCoords_symm_single, finiteFreeEvaluationCoords_apply]
  simpa only [Functor.map_comp, ModuleCat.comp_apply, LinearMap.toMatrix'_apply,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h i j

end FiniteFreeCoordinates

private lemma matrix_of_regular_endomorphisms
    (E : Type u) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
    (V : Scheme.{u})
    {R : Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}} [MonObj R]
    (e : R ⟶ coeff E V) [IsIso e]
    (F : Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) R ⥤ ModuleCat.{u + 1} E)
    [F.Additive] (b : F.obj (Mod.regular R) ≃ₗ[E] E) (v : V)
    (h : ∀ f : Mod.regular R ⟶ Mod.regular R,
      b (F.map f (b.symm 1)) = continuousCoefficientValue E V (inv e ≫ f.hom ≫ e) v)
    {m n : ℕ} (f : Mod.finiteFree R m ⟶ Mod.finiteFree R n) :
    (finiteFreeEvaluationCoords (Mod.regular R) F b n).toLinearMap ∘ₗ (F.map f).hom ∘ₗ
      (finiteFreeEvaluationCoords (Mod.regular R) F b m).symm.toLinearMap =
        ((freeMatrix e f).map (fun s ↦ s v)).mulVecLin := by
  apply finiteFreeEvaluationCoords_matrix
  intro i j
  change b (F.map (biproduct.ι (fun _ : Fin m ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : Fin n ↦ Mod.regular R) i) (b.symm 1)) = _
  rw [Matrix.map_apply, freeMatrix_apply]
  exact h (biproduct.ι (fun _ : Fin m ↦ Mod.regular R) j ≫ f ≫
    biproduct.π (fun _ : Fin n ↦ Mod.regular R) i)

private noncomputable def cokernelCoordinates
    {E : Type v} [CommRing E] {A B : ModuleCat.{w} E}
    {m n : ℕ} (a : A ≃ₗ[E] (Fin m → E)) (b : B ≃ₗ[E] (Fin n → E))
    (f : A ⟶ B) (M : Matrix (Fin n) (Fin m) E)
    (hf : b.toLinearMap ∘ₗ f.hom ∘ₗ a.symm.toLinearMap = M.mulVecLin) :
    (cokernel f : ModuleCat.{w} E) ≃ₗ[E]
      ((Fin n → E) ⧸ LinearMap.range M.mulVecLin) := by
  refine (ModuleCat.cokernelIsoRangeQuotient f).toLinearEquiv.trans
    (Submodule.Quotient.equiv _ _ b ?_)
  rw [← hf, LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.2 a.symm.surjective, Submodule.map_top]

/-- Underlying module inverse image along a scheme map. Source: HRS Example 3.1.
(auxiliary; not a blueprint node) -/
noncomputable def pulledMod (T : Type u) [CommRing T] [TopologicalSpace T]
    [IsTopologicalRing T] {X Y : Scheme.{u}} (p : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (baseCoeff T X)) :=
  ((upperStar Ab.{u + 1} p).mapMod (baseCoeff T X)).obj M

/-- Two presentations of the same sheaf have isomorphic scalar cokernels over a common
base point. Source: HRS Example 3.1; parent proof step 3.

Proof: lift the two points to a point of the fibre product, then take an algebraic
closure of its residue field. Both pulled-back presentations present the same module
over this geometric point. Evaluation at the final object of its pro-etale site is
right exact, since every pro-etale cover of a geometric point splits. It sends the
regular coefficient module to T and sends multiplication by a continuous coefficient
to multiplication by its value at the chosen point, by the adjoint characterization
of the canonical realization. Finite biproduct coordinates therefore identify the two
evaluated cokernels with the scalar matrix cokernels in the statement. Their common
identification with the evaluation of M gives an isomorphism, hence equality in the
skeleton. This uses no field structure on T, no rank comparison, and no Noetherianity.
Empty covering members contain no points; zero rows and columns are ordinary cokernels.
(auxiliary; not a blueprint node) -/
theorem presentationFiberType_eq
    (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (baseCoeff T X))
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (n m : C.I₀ → ℕ)
    (f : ∀ i, Mod.finiteFree ((upperStar Ab.{u + 1} (C.f i)).obj
      (baseCoeff T X)) (m i) ⟶
      Mod.finiteFree ((upperStar Ab.{u + 1} (C.f i)).obj
      (baseCoeff T X)) (n i))
    (e : ∀ i, Nonempty (pulledMod T (C.f i) M ≅
        cokernel (f i)))
    (i j : C.I₀) (v : C.X i) (w : C.X j) (h : C.f i v = C.f j w) :
    presentationFiberType T (C.f i) (f i) v =
      presentationFiberType T (C.f j) (f j) w := by
  classical
  obtain ⟨z, hzi, hzj⟩ := Scheme.Pullback.exists_preimage_pullback v w h
  let Z := pullback (C.f i) (C.f j)
  let Ω := AlgebraicClosure (Z.residueField z)
  let q : Spec (.of Ω) ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫
      Z.fromSpecResidueField z
  let a := q ≫ pullback.fst (C.f i) (C.f j)
  let d := q ≫ pullback.snd (C.f i) (C.f j)
  have had : a ≫ C.f i = d ≫ C.f j := by
    simp only [a, d, Category.assoc, pullback.condition]
  let t₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hq : q t₀ = z :=
    Scheme.fromSpecResidueField_apply z
      ((Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω))) t₀)
  have ha : a t₀ = v := by
    change pullback.fst (C.f i) (C.f j) (q t₀) = v
    rw [hq]
    exact hzi
  have hd : d t₀ = w := by
    change pullback.snd (C.f i) (C.f j) (q t₀) = w
    rw [hq]
    exact hzj
  rw [← ha, ← hd]
  obtain ⟨F, G, hF, hG, hFc, hGc, ⟨α⟩, b, c, hb, hc⟩ :=
    exists_condensedField_compatible_evaluations T X (C.X i) (C.X j) Ω
      (C.f i) (C.f j) a d had t₀
  let := hF
  let := hG
  let := hFc
  let := hGc
  let Ri := (upperStar Ab.{u + 1} (C.f i)).obj (baseCoeff T X)
  let Rj := (upperStar Ab.{u + 1} (C.f j)).obj (baseCoeff T X)
  let bi := finiteFreeEvaluationCoords (Mod.regular Ri) F b
  let bj := finiteFreeEvaluationCoords (Mod.regular Rj) G c
  have hbi := matrix_of_regular_endomorphisms T (C.X i)
    (pullbackComparison T (C.f i)) F b (a t₀) hb (f i)
  have hbj := matrix_of_regular_endomorphisms T (C.X j)
    (pullbackComparison T (C.f j)) G c (d t₀) hc (f j)
  let t : cokernel (F.map (f i)) ≅ cokernel (G.map (f j)) :=
    (PreservesCokernel.iso F (f i)).symm ≪≫
      F.mapIso (e i).some.symm ≪≫ α.app M ≪≫ G.mapIso (e j).some ≪≫
        PreservesCokernel.iso G (f j)
  let ei := cokernelCoordinates (bi (m i)) (bi (n i)) (F.map (f i)) _ hbi
  let ej := cokernelCoordinates (bj (m j)) (bj (n j)) (G.map (f j)) _ hbj
  exact congr_toSkeleton_of_iso
    ((ei.symm.trans (t.toLinearEquiv.trans ej)).toModuleIso)

end AlgebraicGeometry.ProEtale.ContinuousRingUniverse
