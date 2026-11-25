/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # The normalized ordinary identity and composition comparisons

Source: Stacks Tags 03D8 and 0D6D; completed-exchange coherence, proof steps 3--5.
The declarations are relocated unchanged from CompletedExchangeCoherence so that
ordinary coherence can be used independently of its completed counterpart.
(blueprint: lem-weil-pbc-completed-ordinary-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The completed coefficient identification for a composite is the specified composite.
Source: blueprint coherence, proof step 3; Stacks Tag 098T
(blueprint: lem-weil-pbc-completed-ordinary-comparisons).
Proof: the canonical profinite inverse-image comparison respects composition. Its
projections are the constant-section comparisons. The composite coefficient map has
these same projections, so limit uniqueness identifies the maps, and hence the isos. -/
theorem AdicCoefficientDatum.integralRingIso_comp {U V W : Scheme.{t}}
    (h : U ⟶ V) (g : V ⟶ W) :
    d.integralRingIso (h ≫ g) = proEtaleRingCompositeCoefficients h g
      (d.completedRing W) (d.completedRing V) (d.completedRing U)
      (d.integralRingIso g) (d.integralRingIso h) := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  change (d.integralRingIso (h ≫ g)).hom ≫ d.projection U n.unop =
    (proEtaleRingInverseImageComp h g).hom.app (d.completedRing W) ≫
      (proEtaleSheafInverseImage h CommRingCat.{t + 1}).map
        (d.integralRingIso g).hom ≫
      (d.integralRingIso h).hom ≫ d.projection U n.unop
  rw [d.projection_comm, d.projection_comm]
  rw [← Functor.map_comp_assoc, d.projection_comm]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% ((proEtaleRingInverseImageComp h g).hom.naturality
    (d.projection W n.unop))]
  rw [show d.finiteRingIso (h ≫ g) n.unop = proEtaleRingCompositeCoefficients h g
      (d.finiteRing W n.unop) (d.finiteRing V n.unop) (d.finiteRing U n.unop)
      (d.finiteRingIso g n.unop) (d.finiteRingIso h n.unop) by
    apply Iso.ext
    dsimp only [AdicCoefficientDatum.finiteRingIso, proEtaleRingCompositeCoefficients,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom]
    rw [(proEtale_profinite_coefficient_inverse_image d.ringTower).2.2.2.2.2.2.2.2.2.1
      U V W h g (op n.unop)]
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% ((proEtaleRingInverseImageComp h g).hom.naturality
      (pbcLevelConstantComparison W d n.unop).inv)]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    rfl]
  rfl

/-- Ordinary derived pullback composition with the specified coefficient transport.
Source: blueprint coherence, proof step 3; Stacks Tag 0D6D
(blueprint: lem-weil-pbc-completed-ordinary-comparisons). -/
def AdicCoefficientDatum.pullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.pull (h ≫ g) ≅ d.pull g ⋙ d.pull h :=
  eqToIso (congrArg
    (proEtaleRingDerivedPullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    proEtaleCanonicalDerivedPullbackComparison h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

/-- Direct image composition is exactly the conjugate of pullback composition.
Source: blueprint coherence, proof step 3; mate-pasting clause (3)
(blueprint: lem-weil-pbc-completed-ordinary-comparisons). -/
def AdicCoefficientDatum.pushComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.push h ⋙ d.push g ≅ d.push (h ≫ g) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction g (d.completedRing W) (d.completedRing V)
      (d.integralRingIso g)).comp
      (proEtaleRingDerivedAdjunction h (d.completedRing V) (d.completedRing U)
        (d.integralRingIso h)))
    (proEtaleRingDerivedAdjunction (h ≫ g) (d.completedRing W) (d.completedRing U)
      (d.integralRingIso (h ≫ g))) (d.pullComp h g)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralRingIso_id (T : Scheme.{t}) :
    d.integralRingIso (𝟙 T) = (proEtaleRingInverseImageId T).app (d.completedRing T) := by
  apply Iso.ext
  apply limit.hom_ext
  intro n
  change (d.integralRingIso (𝟙 T)).hom ≫ d.projection T n.unop =
    (proEtaleRingInverseImageId T).hom.app (d.completedRing T) ≫ d.projection T n.unop
  rw [d.projection_comm]
  have hn : d.finiteRingIso (𝟙 T) n.unop =
      (proEtaleRingInverseImageId T).app (d.finiteRing T n.unop) := by
    apply Iso.ext
    dsimp only [AdicCoefficientDatum.finiteRingIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, asIso_hom, Iso.app_hom]
    rw [(proEtale_profinite_coefficient_inverse_image d.ringTower).2.2.2.2.2.2.2.1
      T (op n.unop)]
    have hi := congrArg
      (fun a ↦ a ≫ (pbcLevelConstantComparison T d n.unop).hom)
      ((proEtaleRingInverseImageId T).hom.naturality
        (pbcLevelConstantComparison T d n.unop).inv)
    simpa only [Functor.id_map, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      AdicCoefficientDatum.ringTower, proEtaleCoefficientTower, Functor.comp_obj,
      Functor.ofOpSequence, Functor.leftOp, Functor.ofSequence, unop_op,
      adicLisseConstantRing, AdicCoefficientDatum.finiteRing,
      reductionCoefficient, pbcAdicRings, AdicCoefficients.ringSystem] using hi
  rw [hn]
  exact (proEtaleRingInverseImageId T).hom.naturality (d.projection T n.unop)

private theorem modulePushId_generic (T : Scheme.{t})
    (R : Sheaf (ProEt.topology T) CommRingCat.{t + 1})
    (c : (proEtaleSheafInverseImage (𝟙 T) CommRingCat.{t + 1}).obj R ≅ R)
    (hc : c = (proEtaleRingInverseImageId T).app R) :
    ∃! α : proEtaleRingModuleDirectImage (𝟙 T) (R) (R)
        (c) ≅ 𝟭 _,
      ∀ (N : reductionModules T (R)) (U : T.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 T) (R)
          (R) (c)).obj N).val.obj (op U)),
        (α.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m := by
  subst c
  let e := Functor.sheafPushforwardContinuousId'
    (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T) CommRingCat.{t + 1}
      (ProEt.topology T)
  have hc : proEtaleRingDirectImageMap (𝟙 T) (R) (R)
      ((proEtaleRingInverseImageId T).app R) = e.inv.app (R) := by
    unfold proEtaleRingDirectImageMap
    change (proEtaleSheafAdjunction (𝟙 T) CommRingCat.{t + 1}).unit.app _ ≫
      (proEtaleSheafDirectImage (𝟙 T) CommRingCat.{t + 1}).map
        (((conjugateEquiv Adjunction.id
          (proEtaleSheafAdjunction (𝟙 T) CommRingCat.{t + 1})).symm e.inv).app _) = _
    simpa only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.id_obj] using
      (unit_conjugateEquiv_symm Adjunction.id
        (proEtaleSheafAdjunction (𝟙 T) CommRingCat.{t + 1}) e.inv R).symm
  let : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ T)).IsContinuous
      (ProEt.topology T) (ProEt.topology T) := Functor.isContinuous_id _
  let B := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R
  let q := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) T
  let φ : B ⟶ ((proEtaleBaseChange (𝟙 T)).sheafPushforwardContinuous
      RingCat.{t + 1} (ProEt.topology T) (ProEt.topology T)).obj B :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 T) R R ((proEtaleRingInverseImageId T).app R)).hom
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩
  have he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans q.inv _ _ _).app B = 𝟙 B := by
    dsimp only [φ]
    rw [hc]
    ext U x
    change (R.obj.map (q.hom.app U.unop).op ≫ R.obj.map (q.inv.app U.unop).op) x = x
    rw [← R.obj.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
      CategoryTheory.op_id, R.obj.map_id]
    rfl
  let α := SheafOfModules.pushforwardCongr₂ (φ := φ) q.symm he ≪≫
    SheafOfModules.pushforwardId B
  refine ⟨α, ?_, ?_⟩
  · intro N U m
    rfl
  · intro β hβ
    apply Iso.ext
    ext N U m
    exact (hβ N U.unop m).trans (by rfl)

/-- Identity direct image is uniquely fixed by inverse-image restriction on each section.
Source: blueprint coherence, unit normalization in proof step 5; Stacks Tag 03D8
(blueprint: lem-weil-pbc-completed-ordinary-comparisons).
Proof: the base-change identity identifies U times_T T with U. Restriction along its
inverse gives the displayed map. Naturality and the canonical coefficient identity make
it linear; the opposite restriction is inverse. Sectionwise faithfulness gives uniqueness. -/
theorem AdicCoefficientDatum.modulePushId_existsUnique (T : Scheme.{t}) :
    ∃! α : proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T) (d.completedRing T)
        (d.integralRingIso (𝟙 T)) ≅ 𝟭 _,
      ∀ (N : reductionModules T (d.completedRing T)) (U : T.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 T) (d.completedRing T)
          (d.completedRing T) (d.integralRingIso (𝟙 T))).obj N).val.obj (op U)),
        (α.hom.app N).val.app (op U) m =
          N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app U).op m := by
  exact modulePushId_generic T _ _ (integralRingIso_id d T)

/-- The normalized module identity isomorphism, with its section formula retained.
Source: blueprint coherence, proof step 5
(blueprint: lem-weil-pbc-completed-ordinary-comparisons). -/
def AdicCoefficientDatum.modulePushId (T : Scheme.{t}) :=
  (d.modulePushId_existsUnique T).choose

/-- Ordinary pullback identity, derived from its section-normalized ordinary adjunction.
Source: blueprint coherence, proof step 5; Stacks Tag 03D8
(blueprint: lem-weil-pbc-completed-ordinary-comparisons). -/
def AdicCoefficientDatum.pullId (T : Scheme.{t}) : d.pull (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Derived direct-image identity is conjugate to that same pullback identity.
Source: blueprint coherence, proof steps 3 and 5
(blueprint: lem-weil-pbc-completed-ordinary-comparisons). -/
def AdicCoefficientDatum.pushId (T : Scheme.{t}) : d.push (𝟙 T) ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id
    (proEtaleRingDerivedAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))) (d.pullId T)).symm

end AlgebraicGeometry.Scheme
