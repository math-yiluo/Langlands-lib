/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilCompactSupportCohomology
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.DeligneLaumon.ImmersionWeilLocalBehavior
import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlFrameworkOpenExchange
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Frobenius comparison on completed compact-support representatives

Source: blueprint main-20261015, chap-The-Deligne-Laumon-theorem-in-general,
sk-l-dl-general-composition/lem-zl-shriek-composition.proof.md;
prose-10-20, composition-comparison clause
(blueprint: def-zl-frobenius-compact-support-comparison).

The open comparison is the inverse of the open-adjunction mate. The proper
comparison is the direct-image mate. Both use the coefficient-normalized inverse
image compositor. Thus all maps are fixed before any coefficient localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open PurCompactSupport

variable (D : FiniteFieldDatum.{u})
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

set_option linter.unusedSectionVars false in
/-- The geometric-fibre factorization is the base change of the model factorization.
Source: blueprint composition proof, geometric-fibre paragraph
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: apply the base-change functor to c₀.i ≫ c₀.g = f₀.left. Its functoriality
and the defining equalities of zlCompactificationOpen and zlCompactificationProper
give the asserted equality, including on empty schemes. -/
theorem zlGeometricCompactification_comm :
    zlFiberMap D f₀ =
      zlFiberMap D (zlCompactificationOpen D f₀ c₀) ≫
        zlFiberMap D (zlCompactificationProper D f₀ c₀) := by
  let F := Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  have h : f₀ = zlCompactificationOpen D f₀ c₀ ≫
      zlCompactificationProper D f₀ c₀ := by
    apply Over.OverMorphism.ext
    exact c₀.comm
  exact (congrArg (fun h ↦ h.left) (congrArg F.map h)).trans
    (congrArg (fun h ↦ h.left)
      (F.map_comp (zlCompactificationOpen D f₀ c₀) (zlCompactificationProper D f₀ c₀)))

set_option linter.unusedSectionVars false in
/-- The geometric proper part is proper by stability under base change.
Source: blueprint composition proof; Stacks 01W4
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: the geometric-fibre square for the model proper map is Cartesian. Apply
properness under base change to c₀.g; the resulting map is the displayed fibre map. -/
theorem zlGeometricCompactification_isProper :
    IsProper (zlFiberMap D (zlCompactificationProper D f₀ c₀)) := by
  exact MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (zlCompactificationProper D f₀ c₀) c₀.isProper

set_option linter.unusedSectionVars false in
/-- The geometric open part is open by stability under base change.
Source: blueprint composition proof; Stacks 01JU
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: the geometric-fibre square for the model open map is Cartesian. Apply
stability of open immersions under base change to c₀.i. -/
theorem zlGeometricCompactification_isOpenImmersion :
    IsOpenImmersion (zlFiberMap D (zlCompactificationOpen D f₀ c₀)) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (zlCompactificationOpen D f₀ c₀) c₀.isOpenImmersion

/-- Base change of the actual model compactification, retaining its middle model.
Source: blueprint composition proof, geometric-fibre paragraph
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlGeometricCompactification : Compactification (zlFiberMap D f₀) where
  Z := (D.geometricFiber (zlCompactificationMiddle D f₀ c₀)).left
  i := zlFiberMap D (zlCompactificationOpen D f₀ c₀)
  g := zlFiberMap D (zlCompactificationProper D f₀ c₀)
  comm := zlGeometricCompactification_comm D f₀ c₀
  isProper := zlGeometricCompactification_isProper D f₀ c₀
  isOpenImmersion := zlGeometricCompactification_isOpenImmersion D f₀ c₀

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The canonical ordinary completed-coefficient inverse image of geometric Frobenius.
This is an auxiliary ambient functor, not a second constructible pullback definition.
Source: blueprint Frobenius comparison; Stacks 099N
(blueprint: def-zl-frobenius-compact-support-comparison). -/
abbrev zlAmbientFrobenius (T₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] :=
  pull (completed l E) (D.geometricFrobenius T₀).asIso.hom

/-- Pullback around the Frobenius square, with both compositors fixed on coefficients.
Source: blueprint Weil-operation compatibility; Stacks 099N(5)
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlAmbientFrobeniusSquare :
    pull (completed l E) (zlFiberMap D f₀) ⋙ zlAmbientFrobenius D l E X₀ ≅
      zlAmbientFrobenius D l E Y₀ ⋙ pull (completed l E) (zlFiberMap D f₀) :=
  (geometricPullComposition (completed l E) (D.geometricFrobenius X₀).asIso.hom
      (zlFiberMap D f₀) (completedPull_comp l E _ _)).symm ≪≫
    eqToIso (congrArg (fun h ↦ pull (completed l E) h) (zlFrobenius_naturality D f₀)) ≪≫
      geometricPullComposition (completed l E) (zlFiberMap D f₀)
        (D.geometricFrobenius Y₀).asIso.hom (completedPull_comp l E _ _)

/-- The open mate in its unit-normalized direction, before inversion.
Source: blueprint Weil operations; Stacks 03DI
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlFrobeniusOpenMate :
    zlAmbientFrobenius D l E X₀ ⋙
        (openExtension (completed l E) (zlGeometricCompactification D f₀ c₀).i).mapDerivedCategory ⟶
      (openExtension (completed l E) (zlGeometricCompactification D f₀ c₀).i).mapDerivedCategory ⋙
        zlAmbientFrobenius D l E
            (zlCompactificationMiddle D f₀ c₀) :=
  ((mateEquiv
    (openDerivedAdjunction (completed l E) (zlGeometricCompactification D f₀ c₀).i)
    (openDerivedAdjunction (completed l E) (zlGeometricCompactification D f₀ c₀).i)).symm
      (TwoSquare.mk _ _ _ _
        (zlAmbientFrobeniusSquare D (zlCompactificationOpen D f₀ c₀) l E).hom))

/-- Proper direct-image mate of the same normalized Frobenius square.
Source: blueprint Weil operations; Stacks 0D6D
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlFrobeniusProperMate :
    push (completed l E) (zlGeometricCompactification D f₀ c₀).g ⋙
        zlAmbientFrobenius D l E Y₀ ⟶
      zlAmbientFrobenius D l E (zlCompactificationMiddle D f₀ c₀) ⋙
        push (completed l E) (zlGeometricCompactification D f₀ c₀).g :=
  (mateEquiv
    (proEtaleRingDerivedAdjunction (zlGeometricCompactification D f₀ c₀).g
      ((completed l E).ring _) ((completed l E).ring _) ((completed l E).pull _))
    (proEtaleRingDerivedAdjunction (zlGeometricCompactification D f₀ c₀).g
      ((completed l E).ring _) ((completed l E).ring _) ((completed l E).pull _))
    (TwoSquare.mk _ _ _ _
      (zlAmbientFrobeniusSquare D (zlCompactificationProper D f₀ c₀) l E).inv))

open Opposite in
private theorem pushforward_of_ringIso_isEquivalence
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{u + 1}) (S : Sheaf K RingCat.{u + 1})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R) :
    (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{u + 1} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  exact inferInstanceAs
    (SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂).functor.IsEquivalence

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward false in
private theorem geometricPull_isEquivalence {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : Coefficients.{u}) : (pull R g).IsEquivalence := by
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g
    (inferInstance : WeaklyEtale g) trivial
  let : (MorphismProperty.Over.map (P := @WeaklyEtale) ⊤
      (inferInstance : WeaklyEtale g)).IsEquivalence :=
    (proEtaleIsoPostcompose_equivalence g).1
  let : (proEtaleBaseChange g).IsEquivalence :=
    adj.isEquivalence_right_of_isEquivalence_left
  let e : X.ProEt ≌ Y.ProEt :=
    { functor := proEtaleIsoPostcompose g
      inverse := proEtaleBaseChange g
      unitIso := asIso adj.unit
      counitIso := asIso adj.counit
      functor_unitIso_comp := adj.left_triangle_components }
  let : e.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  let : e.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) := by
    change (proEtaleBaseChange g).IsContinuous _ _
    infer_instance
  let a := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  let : IsIso a.unit :=
    (proEtaleIsoInverseImage_equivalence.{u, u + 2, 0, 0} g CommRingCat.{u + 1}).2.1
  let : IsIso (proEtaleRingDirectImageMap g (R.ring Y) (R.ring X) (R.pull g)) := by
    unfold proEtaleRingDirectImageMap
    infer_instance
  let d : R.ring Y ≅ (proEtaleSheafDirectImage g CommRingCat.{u + 1}).obj (R.ring X) :=
    asIso (proEtaleRingDirectImageMap g (R.ring Y) (R.ring X) (R.pull g))
  let RX := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.ring X)
  let RY := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.ring Y)
  let c : RY ≅ (e.inverse.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology Y) (ProEt.topology X)).obj RX :=
    (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso d
  let : (proEtaleRingModuleDirectImage g (R.ring Y) (R.ring X)
      (R.pull g)).IsEquivalence :=
    show (SheafOfModules.pushforward.{u + 1} (F := e.inverse) c.hom).IsEquivalence from
      pushforward_of_ringIso_isEquivalence _ _ e RX RY c
  let : (proEtaleRingModulePullback g (R.ring Y) (R.ring X)
      (R.pull g)).IsEquivalence :=
    (proEtaleRingModuleAdjunction g (R.ring Y) (R.ring X)
      (R.pull g)).isEquivalence_left_of_isEquivalence_right
  exact Functor.isEquivalence_mapDerivedCategory _

/-- Both prescribed mates are invertible for geometric Frobenius.
Source: blueprint prose-10-20; Stacks 099N and 03DI
(blueprint: def-zl-frobenius-compact-support-comparison).
Proof: geometric Frobenius and its middle-model map are scheme isomorphisms.
Their exact inverse-image equivalences identify each square with an identity
square. Transpose the normalized pullback square under the open adjunction and
the proper derived adjunction. Transposing the inverse square gives inverses;
the two triangle identities prove the inverse equations. This works in the
ambient completed-ring module categories, before imposing constructibility. -/
theorem zlFrobeniusMates_isIso :
    IsIso (zlFrobeniusOpenMate D f₀ c₀ l E) ∧
      IsIso (zlFrobeniusProperMate D f₀ c₀ l E) := by
  let : (zlAmbientFrobenius D l E X₀).IsEquivalence :=
    geometricPull_isEquivalence (D.geometricFrobenius X₀).asIso.hom (completed l E)
  let : (zlAmbientFrobenius D l E Y₀).IsEquivalence :=
    geometricPull_isEquivalence (D.geometricFrobenius Y₀).asIso.hom (completed l E)
  let : (zlAmbientFrobenius D l E (zlCompactificationMiddle D f₀ c₀)).IsEquivalence :=
    geometricPull_isEquivalence
      (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀)).asIso.hom (completed l E)
  constructor
  · exact isIso_inverseMate_of_equivalences _ _
      (zlAmbientFrobeniusSquare D (zlCompactificationOpen D f₀ c₀) l E)
  · exact isIso_mateEquiv_of_isEquivalence _ _
      (TwoSquare.mk _ _ _ _
        (zlAmbientFrobeniusSquare D (zlCompactificationProper D f₀ c₀) l E).inv)

/-- The canonical compact-support Frobenius comparison on completed representatives.
It is proper exchange followed by the inverse open mate.
Source: blueprint prose-10-20, compact-support clause
(blueprint: def-zl-frobenius-compact-support-comparison). -/
def zlCompactSupportFrobenius :
    image (completed l E) (zlGeometricCompactification D f₀ c₀) ⋙
        zlAmbientFrobenius D l E Y₀ ≅
      zlAmbientFrobenius D l E X₀ ⋙
        image (completed l E) (zlGeometricCompactification D f₀ c₀) := by
  letI := (zlFrobeniusMates_isIso D f₀ c₀ l E).1
  letI := (zlFrobeniusMates_isIso D f₀ c₀ l E).2
  exact (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (asIso (zlFrobeniusProperMate D f₀ c₀ l E)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (zlFrobeniusOpenMate D f₀ c₀ l E)).symm _ ≪≫
    Functor.associator _ _ _

end WeilConjectures
