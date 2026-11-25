/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Finite constant-coefficient pullback of the regular module -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d w u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingDirectImageMap
  AlgebraicGeometry.Scheme.proEtaleConstantRingComparison
  CategoryTheory.constantSheaf Padic Padic.coefficientExtensionIntegers

private theorem adjoint_unit_isIso
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (adj : L ⊣ SheafOfModules.pushforward φ) :
    IsIso ((adj.homEquiv _ _).symm (SheafOfModules.unitToPushforwardObjUnit φ)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← (adj.homEquiv _ _).bijective.of_comp_iff',
    ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
  convert! (SheafOfModules.bijective_pushforwardSections φ M).comp
    (SheafOfModules.unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [SheafOfModules.pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]

private def adjointUnitIso
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (adj : L ⊣ SheafOfModules.pushforward φ) :
    L.obj (SheafOfModules.unit S) ≅ SheafOfModules.unit R :=
  @asIso _ _ _ _ ((adj.homEquiv _ _).symm (SheafOfModules.unitToPushforwardObjUnit φ))
    (adjoint_unit_isIso φ L adj)

private theorem adjointUnitIso_hom
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (adj : L ⊣ SheafOfModules.pushforward φ) :
    (adj.homEquiv _ _) (adjointUnitIso φ L adj).hom =
      SheafOfModules.unitToPushforwardObjUnit φ :=
  Equiv.apply_symm_apply _ _

attribute [local irreducible] adjointUnitIso

private def transportedUnitIso
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (adj : L ⊣ SheafOfModules.pushforward φ)
    {M : SheafOfModules.{w} S} {N : SheafOfModules.{w} R}
    (aS : SheafOfModules.unit S ≅ M) (aR : SheafOfModules.unit R ≅ N) :
    L.obj M ≅ N :=
  L.mapIso aS.symm ≪≫ adjointUnitIso φ L adj ≪≫ aR

private theorem transportedUnitIso_adjoint
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} [F.IsContinuous J K] [F.Final]
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (L : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R)
    (adj : L ⊣ SheafOfModules.pushforward φ)
    {M : SheafOfModules.{w} S} {N : SheafOfModules.{w} R}
    (aS : SheafOfModules.unit S ≅ M) (aR : SheafOfModules.unit R ≅ N) :
    (adj.homEquiv _ _) (transportedUnitIso φ L adj aS aR).hom =
      aS.inv ≫ SheafOfModules.unitToPushforwardObjUnit φ ≫
        (SheafOfModules.pushforward φ).map aR.hom := by
  dsimp only [transportedUnitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    adjointUnitIso_hom]
  rfl

attribute [local irreducible] transportedUnitIso

private def pushforward_unit_iso
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{w}) :
    SheafOfModules.unit ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R) ≅
      (SheafOfModules.pushforward (F := F) (𝟙 _)).obj (SheafOfModules.unit R) :=
  Iso.refl _

private def pushforward_unit_iso_of_eq
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{w})
    (S : Sheaf J RingCat.{w})
    (e : S = (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    SheafOfModules.unit S ≅
      (SheafOfModules.pushforward (F := F) (eqToHom e)).obj (SheafOfModules.unit R) := by
  subst S
  exact pushforward_unit_iso F R

private theorem pushforward_unit_iso_of_eq_sections
    {C : Type a} [Category.{b} C] {D : Type c} [Category.{d} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{w})
    (S : Sheaf J RingCat.{w})
    (e : S = (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
    (U : Cᵒᵖ) (x : S.obj.obj U) :
    HEq ((pushforward_unit_iso_of_eq F R S e).hom.val.app U x) x := by
  subst S
  rfl

attribute [local irreducible] pushforward_unit_iso_of_eq

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def coefficientEvaluationUnit (T : Scheme.{u}) (n : ℕ) :
    SheafOfModules.unit (SemilinearSections.ring (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T n)) ≅
      (SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)) :=
  pushforward_unit_iso_of_eq _ _ _
    (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm

attribute [local irreducible] coefficientEvaluationUnit

private theorem coefficientEvaluationUnit_sections (T : Scheme.{u}) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : (SpTowerShriek.B l E T n).obj.obj U) :
    HEq ((coefficientEvaluationUnit l E T n).hom.val.app U x) x :=
by
  unfold coefficientEvaluationUnit
  exact pushforward_unit_iso_of_eq_sections _ _
    (SemilinearSections.ring (Scheme.ProEt.topology T) (SpTowerShriek.B l E T n))
    (SemilinearSections.evaluation_ring.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) n).symm U x

end AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def finiteRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  Scheme.proEtaleRingDirectImageMap f (SpTowerShriek.B l E Y n)
    (SpTowerShriek.B l E X n)
    (Scheme.proEtaleConstantRingComparison f (SpTowerShriek.R l E n))

private theorem finiteRingMap_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    finiteRingMap l E f n =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) := by
  unfold finiteRingMap Scheme.proEtaleRingDirectImageMap
    Scheme.proEtaleConstantRingComparison
  change (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    (Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1} _) = _
  unfold Scheme.proEtaleConstantInverseImageMap
  exact Equiv.apply_symm_apply _ _

private def finiteUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((SpTowerShriek.ev l E Y n).obj (coefficient Y (Arings l E Y))) ≅
      (SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X)) :=
  transportedUnitIso (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := SemilinearSections.ring (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n))
    (R := SemilinearSections.ring (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n))
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteRingMap l E f n))
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)
    (coefficientEvaluationUnit l E Y n) (coefficientEvaluationUnit l E X n)

end AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finiteUnitIso_normalization {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEtᵒᵖ) (x : (SpTowerShriek.B l E Y n).obj.obj U)
    (x' : ((SpTowerShriek.ev l E Y n).obj
      (coefficient Y (Arings l E Y))).val.obj U) (hx : HEq x x') :
    HEq (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
        _ _ (finiteUnitIso l E f n).hom).val.app U x')
      ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x) := by
  have hh := transportedUnitIso_adjoint (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := SemilinearSections.ring (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n))
    (R := SemilinearSections.ring (Scheme.ProEt.topology X) (SpTowerShriek.B l E X n))
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (finiteRingMap l E f n))
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)
    (coefficientEvaluationUnit l E Y n) (coefficientEvaluationUnit l E X n)
  refine (heq_of_eq (congrArg (fun q ↦ q.val.app U x') hh)).trans ?_
  let aY := coefficientEvaluationUnit l E Y n
  have hi : HEq (aY.inv.val.app U x') x := by
    have he := congrArg (fun k ↦ k.val.app U x') aY.inv_hom_id
    exact ((coefficientEvaluationUnit_sections l E Y n U
      (aY.inv.val.app U x')).symm.trans (heq_of_eq he)).trans hx.symm
  change HEq ((coefficientEvaluationUnit l E X n).hom.val.app
    ((Scheme.proEtaleBaseChange f).op.obj U)
    ((finiteRingMap l E f n).hom.app U (aY.inv.val.app U x'))) _
  have hs := coefficientEvaluationUnit_sections l E X n
    ((Scheme.proEtaleBaseChange f).op.obj U)
    ((finiteRingMap l E f n).hom.app U (aY.inv.val.app U x'))
  have he := congrArg (fun q ↦ q.hom.app U (aY.inv.val.app U x'))
    (finiteRingMap_eq l E f n)
  exact hs.trans (heq_of_eq (he.trans (congrArg _ (eq_of_heq hi))))

end AlgebraicGeometry.ProEtale.SpTowerClasses

namespace AlgebraicGeometry.ProEtale.SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] finiteUnitIso

/-- The actual finite constant-ring adjunction preserves its regular module,
with its transpose fixed on every section.
Source: Stacks 03D2 and 03D7; Mathlib's pullback-unit argument in
`SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal`.
(blueprint: lem-sfb-tower-class-finite-unit).

Proof: direct image preserves global module sections since base change on the
pro-etale sites preserves terminal objects and is therefore final. The regular
module represents global sections. Thus composition with the adjoint of the
canonical unital ring map is a bijection on every outgoing Hom set, so that
adjoint is invertible by Yoneda. Transport the two regular modules through the
identity-on-carriers evaluation comparisons. Naturality of the Hom equivalence
identifies its transpose with the original unital ring map. Its equality with
the constant direct-image map is the inverse law of the ring-sheaf adjunction.
This uses neither a nonempty-chart assumption nor finiteness of the ring. -/
theorem exists_finiteUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃ d : (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        ((SpTowerShriek.ev l E Y n).obj (coefficient Y (Arings l E Y))) ≅
      (SpTowerShriek.ev l E X n).obj (coefficient X (Arings l E X)),
      ∀ (U : Y.ProEtᵒᵖ) (x : (SpTowerShriek.B l E Y n).obj.obj U)
        (x' : ((SpTowerShriek.ev l E Y n).obj
          (coefficient Y (Arings l E Y))).val.obj U),
        HEq x x' → HEq
          (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
            _ _ d.hom).val.app U x')
          ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
            (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U x) := by
  exact ⟨finiteUnitIso l E f n, finiteUnitIso_normalization l E f n⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
