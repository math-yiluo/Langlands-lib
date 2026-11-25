/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! Existence of the normalized supported source for a projection trace.
Source: diagonal tower trace proof paragraph (2), construction step 9
(blueprint: lem-sfb-diagonal-trace-supported-source-existence).
-/

@[expose] public noncomputable section
set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u a b v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

-- Resolve before applying the exact closed pushforward. Naturality reduces the
-- assertion to the given derived functor's computation on K-injectives.
private theorem unit_isIso_on_exact_image
    {A : Type a} {B : Type b} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (R : DiagonalRightDerived G) (K : CochainComplex A ℤ) :
    IsIso (R.η.app ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  obtain ⟨I, hI, j, _, hj⟩ :=
    CategoryTheory.Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have : I.IsKInjective := hI
  have : QuasiIso j := hj
  let Fj := (F.mapHomologicalComplex (.up ℤ)).map j
  have : QuasiIso Fj := inferInstance
  have : QuasiIso ((G.mapHomologicalComplex (.up ℤ)).map Fj) :=
    inferInstanceAs (QuasiIso (((F ⋙ G).mapHomologicalComplex (.up ℤ)).map j))
  have := R.computation ((F.mapHomologicalComplex (.up ℤ)).obj I) inferInstance
  have h := R.η.naturality Fj
  dsimp only [Functor.comp_map] at h
  have : IsIso (R.η.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      R.R.map (DerivedCategory.Q.map Fj)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (R.R.map (DerivedCategory.Q.map Fj))

private theorem rightSingle_isIso_on_exact_image
    {A : Type a} {B : Type a} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesKInjectiveComplexes]
    [PreservesFiniteLimits (F ⋙ G)] [PreservesFiniteColimits (F ⋙ G)]
    (R : DiagonalRightDerived G) (N : A) :
    IsIso (diagonalTraceRightSingle G R (F.obj N)) := by
  let e := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app N
  have := unit_isIso_on_exact_image F G R
    ((HomologicalComplex.single A (.up ℤ) 0).obj N)
  have h := R.η.naturality e.inv
  dsimp only [Functor.comp_map, Functor.comp_obj] at h
  have : IsIso (R.η.app ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj N)) ≫
      R.R.map (DerivedCategory.Q.map e.inv)) := by
    rw [← h]
    infer_instance
  have : IsIso (R.η.app ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj N))) :=
    IsIso.of_isIso_comp_right _ (R.R.map (DerivedCategory.Q.map e.inv))
  unfold diagonalTraceRightSingle
  infer_instance

private def residueTower (l : ℕ) : ℕᵒᵖ ⥤ CommRingCat.{u + 1} :=
  Functor.ofOpSequence
    (X := fun n ↦ CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (fun n ↦ CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) (ZMod (l ^ (n + 1)))).comp
        ULift.ringEquiv.toRingHom)))

private def residueTowerIso (l : ℕ) (X : Scheme.{u}) :
    Scheme.proEtaleCoefficientTower X (residueTower l) ≅ Scheme.purTwistZlTower X l :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (fun f ↦ (NatTrans.ofOpSequence
      (F := Scheme.proEtaleCoefficientTower X (residueTower l))
      (G := Scheme.purTwistZlTower X l)
      (fun _ ↦ 𝟙 _) (fun n ↦ by
        simp [Scheme.proEtaleCoefficientTower, residueTower, Scheme.purTwistZlTower,
          Scheme.purTwistZlTowerOfUniverses,
          Scheme.purTwistFiniteTransitionOfUniverses])).naturality f)

private theorem coefficientMap_isIso (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) : IsIso (diagonalCompletedCoefficientMap l f) := by
  let Q := residueTower.{u} l
  have (n : ℕᵒᵖ) : NeZero (l ^ (n.unop + 1)) :=
    ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have (n : ℕᵒᵖ) : Finite (Q.obj n) := by
    change Finite (ULift (ZMod (l ^ (n.unop + 1))))
    infer_instance
  let c (W : Scheme.{u}) := HasLimit.isoOfNatIso (residueTowerIso l W)
  let L := Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}
  have := (Scheme.proEtale_profinite_coefficient_inverse_image Q).2.1 X S f
  let t := L.mapIso (c S).symm ≪≫
    asIso (Scheme.proEtaleProfiniteComparison f Q) ≪≫ c X
  suffices h : diagonalCompletedCoefficientMap l f = t.hom by
    rw [h]
    infer_instance
  apply limit.hom_ext
  rintro ⟨n⟩
  dsimp only [diagonalCompletedCoefficientMap, t, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom]
  simp only [limit.lift_π, Category.assoc]
  dsimp only [c]
  rw [HasLimit.isoOfNatIso_hom_π]
  simp only [asIso_hom]
  rw [reassoc_of% (Scheme.proEtale_profinite_coefficient_inverse_image Q).2.2.1 X S f (op n)]
  rw [← Category.assoc, ← Category.assoc, ← L.map_comp]
  rw [HasLimit.isoOfNatIso_inv_π]
  simp only [L.map_comp, Category.assoc]
  dsimp only [residueTowerIso, Iso.trans_hom, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    Category.comp_id, Scheme.proEtaleConstantComparison]
  let p : L.obj (Scheme.purTwistZlCompletion S l) ⟶
      L.obj (Scheme.purTwistFiniteRing S l n) := L.map (Scheme.purTwistZlProjection S l n)
  let a : L.obj (Scheme.purTwistFiniteRing S l n) ⟶ Scheme.purTwistFiniteRing X l n :=
    Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
  change p ≫ a = p ≫ L.map (𝟙 (Scheme.purTwistFiniteRing S l n)) ≫ a ≫
    𝟙 (Scheme.purTwistFiniteRing X l n)
  simp only [Category.comp_id]
  calc
    p ≫ a = p ≫ 𝟙 _ ≫ a := by rw [Category.id_comp]
    _ = p ≫ L.map (𝟙 (Scheme.purTwistFiniteRing S l n)) ≫ a :=
      (congrArg (fun z : L.obj (Scheme.purTwistFiniteRing S l n) ⟶
          L.obj (Scheme.purTwistFiniteRing S l n) ↦ p ≫ z ≫ a)
        (L.map_id (Scheme.purTwistFiniteRing S l n))).symm

private instance residueTower_finite (l : ℕ) [Fact l.Prime] (n : ℕᵒᵖ) :
    Finite ((residueTower.{u} l).obj n) := by
  have : NeZero (l ^ (n.unop + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  change Finite (ULift (ZMod (l ^ (n.unop + 1))))
  infer_instance

private def coefficientIso (l : ℕ) [Fact l.Prime] {X S : Scheme.{u}} (f : X ⟶ S) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
      (Scheme.purTwistZlCompletion S l) ≅ Scheme.purTwistZlCompletion X l :=
  @asIso _ _ _ _ (diagonalCompletedCoefficientMap l f) (coefficientMap_isIso l f)

private theorem coefficientIso_π (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) :
    (coefficientIso l f).hom ≫ Scheme.purTwistZlProjection X l n =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (Scheme.purTwistZlProjection S l n) ≫
      Scheme.proEtaleConstantInverseImageMap f CommRingCat.{u + 1}
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) := by
  exact limit.lift_π _ (op n)

private theorem coefficientIso_comp (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coefficientIso l (f ≫ g) =
      (Scheme.proEtaleRingInverseImageComp f g).app (Scheme.purTwistZlCompletion Z l) ≪≫
        (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).mapIso
          (coefficientIso l g) ≪≫ coefficientIso l f := by
  apply Iso.ext
  apply limit.hom_ext
  rintro ⟨n⟩
  change (coefficientIso l (f ≫ g)).hom ≫ Scheme.purTwistZlProjection X l n =
    (Scheme.proEtaleRingInverseImageComp f g).hom.app (Scheme.purTwistZlCompletion Z l) ≫
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (coefficientIso l g).hom ≫
      (coefficientIso l f).hom ≫ Scheme.purTwistZlProjection X l n
  rw [coefficientIso_π, coefficientIso_π]
  rw [← Functor.map_comp_assoc, coefficientIso_π, Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% ((Scheme.proEtaleRingInverseImageComp f g).hom.naturality
    (Scheme.purTwistZlProjection Z l n))]
  have H := Scheme.proEtale_profinite_coefficient_inverse_image (residueTower.{u} l)
  exact congrArg ((Scheme.proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).map
      (Scheme.purTwistZlProjection Z l n) ≫ ·)
    (H.2.2.2.2.2.2.2.2.2.1 X Y Z f g (op n))

private theorem coefficientIso_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    coefficientIso l (𝟙 X) =
      (Scheme.proEtaleRingInverseImageId X).app (Scheme.purTwistZlCompletion X l) := by
  apply Iso.ext
  apply limit.hom_ext
  rintro ⟨n⟩
  change (coefficientIso l (𝟙 X)).hom ≫ Scheme.purTwistZlProjection X l n =
    (Scheme.proEtaleRingInverseImageId X).hom.app (Scheme.purTwistZlCompletion X l) ≫
      Scheme.purTwistZlProjection X l n
  rw [coefficientIso_π]
  have H := Scheme.proEtale_profinite_coefficient_inverse_image (residueTower.{u} l)
  rw [show Scheme.proEtaleConstantInverseImageMap (𝟙 X) CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) = _ from
    H.2.2.2.2.2.2.2.1 X (op n)]
  exact (Scheme.proEtaleRingInverseImageId X).hom.naturality
    (Scheme.purTwistZlProjection X l n)

-- Keep the limit object and its coefficient morphism folded in subsequent module
-- constructions. Their projection API above supplies all required coherence.
attribute [local irreducible] Scheme.purTwistZlCompletionOfUniverses
  diagonalCompletedCoefficientMap

private def completedPushComparison (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    diagonalTracePush l f ≅ Scheme.proEtaleRingModuleDirectImage f
      (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l)
      (@asIso _ _ _ _ (diagonalCompletedCoefficientMap l f) (coefficientMap_isIso l f)) :=
  NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)))
    (by intros; ext U x; rfl)

private theorem completedPush_preservesKInjective (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (diagonalTracePush l f).PreservesKInjectiveComplexes := by
  let c := @asIso _ _ _ _ (diagonalCompletedCoefficientMap l f) (coefficientMap_isIso l f)
  obtain ⟨ha, _, hl, hc, ⟨adj⟩⟩ := Scheme.proEtaleRingModuleOperations_properties f
    (Scheme.purTwistZlCompletion S l) (Scheme.purTwistZlCompletion X l) c
  have := ha
  have := hl
  have := hc
  have adj' := adj.ofNatIsoRight (completedPushComparison l f).symm
  exact adj'.preservesKInjectiveComplexes

private theorem completedPush_comp (l : ℕ) [Fact l.Prime]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ e : diagonalTracePush l f ⋙ diagonalTracePush l g ≅ diagonalTracePush l (f ≫ g),
      ∀ N, (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Z (Scheme.purTwistZlCompletion Z l))).map (e.hom.app N) =
        (lowerStarComp AddCommGrpCat.{u + 1} f g).hom.app
          ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj N) := by
  obtain ⟨d, _, hd, _⟩ := Scheme.proEtale_tensor_composition_unit f g
    (Scheme.purTwistZlCompletion Z l) (Scheme.purTwistZlCompletion Y l)
    (Scheme.purTwistZlCompletion X l) (coefficientIso l g) (coefficientIso l f)
    (coefficientIso l (f ≫ g)) (coefficientIso_comp l f g)
  let e := Functor.isoWhiskerRight (completedPushComparison l f) (diagonalTracePush l g) ≪≫
    Functor.isoWhiskerLeft _ (completedPushComparison l g) ≪≫ d.symm ≪≫
    (completedPushComparison l (f ≫ g)).symm
  refine ⟨e, fun N ↦ ?_⟩
  have hi : ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Z (Scheme.purTwistZlCompletion Z l))).mapIso (e.app N)).symm =
      ((lowerStarComp AddCommGrpCat.{u + 1} f g).app
        ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj N)).symm := by
    apply Iso.ext
    ext U x
    change (d.hom.app N).val.app U x =
      (((lowerStarComp AddCommGrpCat.{u + 1} f g).inv.app
        ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj N)).hom.app U) x
    erw [lowerStarComp_inv_app_hom_app]
    exact hd N U.unop x
  exact congrArg Iso.inv hi

private theorem completedPush_id (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ∃ e : diagonalTracePush l (𝟙 X) ≅ 𝟭 _,
      ∀ N, (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).map (e.hom.app N) =
        (lowerStarId AddCommGrpCat.{u + 1} X).hom.app
          ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj N) := by
  obtain ⟨d, hd, _⟩ := Scheme.modulePushId_generic X (Scheme.purTwistZlCompletion X l)
    (coefficientIso l (𝟙 X)) (coefficientIso_id l X)
  refine ⟨completedPushComparison l (𝟙 X) ≪≫ d, fun N ↦ ?_⟩
  ext U x
  change (d.hom.app N).val.app U x = _
  exact hd N U.unop x

private theorem completedPush_congr (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (N : DiagonalCompleted l X) :
    (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map
      ((eqToIso (congrArg (diagonalTracePush l) h)).hom.app N) =
      (lowerStarCongr AddCommGrpCat.{u + 1} h).hom.app
        ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj N) := by
  subst g
  rfl

/-- Completed module pushforward along a section followed by its retraction is the
identity, with the canonical underlying additive-sheaf comparison.

Source: diagonal tower trace proof paragraph (2), construction step 9
(blueprint: lem-sfb-diagonal-trace-supported-source-existence).
Proof: identify inverse image of the completed coefficient ring with the completed
coefficient ring using its finite residue-ring projections. Those projections also
verify the composition and identity coherence. Apply the module composition and
identity comparisons, and transport along the section equation. Their underlying
additive maps are the canonical lower-star composition and identity maps.
-/
private theorem completedPush_section (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (s : Y ⟶ X) (f : X ⟶ Y) (h : s ≫ f = 𝟙 Y) :
    ∃ e : diagonalTracePush l s ⋙ diagonalTracePush l f ≅ 𝟭 _,
      ∀ N, (SheafOfModules.toSheaf.{u + 1}
        (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map (e.hom.app N) =
        ((lowerStarComp AddCommGrpCat.{u + 1} s f) ≪≫
          lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
          lowerStarId AddCommGrpCat.{u + 1} Y).hom.app
            ((SheafOfModules.toSheaf.{u + 1}
              (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).obj N) := by
  obtain ⟨c, hc⟩ := completedPush_comp l s f
  obtain ⟨i, hi⟩ := completedPush_id l Y
  refine ⟨c ≪≫ eqToIso (congrArg (diagonalTracePush l) h) ≪≫ i, fun N ↦ ?_⟩
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, hc, hi]
  rw [completedPush_congr l h N]

private theorem restrictScalars_exact
    {C : Type a} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{b}] [J.WEqualsLocallyBijective AddCommGrpCat.{b}]
    {R S : Sheaf J RingCat.{b}} (r : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{b} r) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{b} r) := by
  let F := SheafOfModules.restrictScalars.{b} r
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} R) :=
    (moduleSheaves_colimits_forgetful R).2.2.1
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S) :=
    (moduleSheaves_colimits_forgetful S).2.2.1
  have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{b} S))
  have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{b} R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{b} S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{b} R) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R),
    preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{b} R)⟩

private theorem diagonalPush_exact (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)] :
    PreservesFiniteLimits (diagonalTracePush l (diagonalImmersion Y)) ∧
      PreservesFiniteColimits (diagonalTracePush l (diagonalImmersion Y)) := by
  let I := (diagonalImmersion Y).ker
  let V : (diagonalSurface Y).Opens := I.support.compl
  let U : (diagonalSurface Y).ProEt := Scheme.ProEt.mk V.ι
  have : IsOpenImmersion U.hom := by
    change IsOpenImmersion V.ι
    infer_instance
  have : QuasiCompact U.hom := by
    change QuasiCompact V.ι
    infer_instance
  have hU : Set.range U.hom = (Set.range (diagonalImmersion Y))ᶜ := by
    change Set.range V.ι.base = (Set.range (diagonalImmersion Y).base)ᶜ
    simp only [Scheme.Opens.range_ι, V, TopologicalSpace.Closeds.coe_compl,
      I, Scheme.Hom.support_ker,
      (diagonalImmersion Y).isClosedEmbedding.isClosed_range.closure_eq]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hl, hc, _⟩ :=
    Scheme.proEtale_ringed_open_closed (diagonalImmersion Y) U hU
      (Scheme.purTwistZlCompletion (diagonalSurface Y) l)
  have := hl
  have := hc
  obtain ⟨hsL, hsC⟩ := restrictScalars_exact
    ((sheafCompose (Scheme.ProEt.topology (ProjectiveLine Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (diagonalCompletedCoefficientMap l (diagonalImmersion Y)))
  have := hsL
  have := hsC
  unfold diagonalTracePush
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

-- These equalities isolate the supported source and its underlying additive sheaf.
-- Their API avoids repeated kernel conversion of module actions.
private theorem completedSource_eq (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    diagonalCompletedSource l Y = (diagonalTracePush l (diagonalImmersion Y)).obj
      (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) := by
  rfl

private theorem completedForget_obj_eq (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : DiagonalCompleted l X) :
    (diagonalCompletedRestriction l X ⋙ diagonalForget l X).obj M =
      (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).obj M := by
  rfl

private theorem completedForget_map_heq (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    {M N : DiagonalCompleted l X} (f : M ⟶ N) :
    HEq ((diagonalCompletedRestriction l X ⋙ diagonalForget l X).map f)
      ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))).map f) := by
  rfl

private theorem natTrans_app_heq_of_eq
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (α : F ⟶ G) {M N : C} (h : M = N) :
    HEq (α.app M) (α.app N) := by
  subst N
  rfl

private theorem map_eqToHom_comp_heq
    {C : Type a} {D : Type b} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {M N : C} (h : M = N) {P : D} (k : F.obj N ⟶ P) :
    HEq (F.map (eqToHom h) ≫ k) k := by
  subst N
  change HEq (F.map (𝟙 M) ≫ k) k
  exact heq_of_eq ((congrArg (fun z ↦ z ≫ k) (F.map_id M)).trans (Category.id_comp k))

private theorem completedPush_transport_normalization (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (s : Y ⟶ X) (f : X ⟶ Y) (h : s ≫ f = 𝟙 Y)
    (e : diagonalTracePush l s ⋙ diagonalTracePush l f ≅ 𝟭 _)
    (he : ∀ N, (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map (e.hom.app N) =
      ((lowerStarComp AddCommGrpCat.{u + 1} s f) ≪≫
        lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
        lowerStarId AddCommGrpCat.{u + 1} Y).hom.app ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).obj N))
    (N : DiagonalCompleted l Y) (M : DiagonalCompleted l X)
    (hm : M = (diagonalTracePush l s).obj N) :
    HEq ((diagonalCompletedRestriction l Y ⋙ diagonalForget l Y).map
      ((e.app N).symm ≪≫ (diagonalTracePush l f).mapIso (eqToIso hm).symm).inv)
      (((lowerStarComp AddCommGrpCat.{u + 1} s f) ≪≫
        lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
        lowerStarId AddCommGrpCat.{u + 1} Y).hom.app
          ((diagonalCompletedRestriction l Y ⋙ diagonalForget l Y).obj N)) := by
  let c := (e.app N).symm ≪≫ (diagonalTracePush l f).mapIso (eqToIso hm).symm
  let α := ((lowerStarComp AddCommGrpCat.{u + 1} s f) ≪≫
    lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫ lowerStarId AddCommGrpCat.{u + 1} Y).hom
  refine (completedForget_map_heq l Y c.inv).trans ?_
  have hmid : HEq ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map c.inv)
      (α.app ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).obj N)) := by
    change HEq ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map
      ((diagonalTracePush l f).map (eqToHom hm) ≫ e.hom.app N)) _
    rw [Functor.map_comp]
    have hh := heq_of_eq (he N)
    exact (map_eqToHom_comp_heq (diagonalTracePush l f ⋙
      SheafOfModules.toSheaf.{u + 1}
        (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l)))
      hm ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing Y (Scheme.purTwistZlCompletion Y l))).map (e.hom.app N))).trans hh
  exact hmid.trans (natTrans_app_heq_of_eq α (completedForget_obj_eq l Y N)).symm

private def supportedIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (e : diagonalTracePush l (diagonalImmersion Y) ⋙ diagonalTracePush l f ≅ 𝟭 _) :
    SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)) ≅
      (diagonalTracePush l f).obj (diagonalCompletedSource l Y) :=
  (e.app (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))).symm ≪≫
    (diagonalTracePush l f).mapIso (eqToIso (completedSource_eq l Y)).symm

private theorem supportedIso_normalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y))
    (e : diagonalTracePush l (diagonalImmersion Y) ⋙ diagonalTracePush l f ≅ 𝟭 _)
    (he : ∀ N, (SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing (ProjectiveLine Y)
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))).map (e.hom.app N) =
      ((lowerStarComp AddCommGrpCat.{u + 1} (diagonalImmersion Y) f) ≪≫
        lowerStarCongr AddCommGrpCat.{u + 1} h ≪≫
        lowerStarId AddCommGrpCat.{u + 1} (ProjectiveLine Y)).hom.app
          ((SheafOfModules.toSheaf.{u + 1}
      (Scheme.purTwistRing (ProjectiveLine Y)
        (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))).obj N)) :
    supportedSourceNormalization l Y f (supportedIso l Y f e) h := by
  exact completedPush_transport_normalization l (diagonalImmersion Y) f h e he
    (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) (diagonalCompletedSource l Y)
    (completedSource_eq l Y)

private theorem supported_acyclic (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (R : DiagonalRightDerived (diagonalTracePush l f))
    (e : diagonalTracePush l (diagonalImmersion Y) ⋙ diagonalTracePush l f ≅ 𝟭 _) :
    IsIso (diagonalTraceRightSingle (diagonalTracePush l f) R
      (diagonalCompletedSource l Y)) := by
  rw [completedSource_eq]
  obtain ⟨hl, hc⟩ := diagonalPush_exact l Y
  have := hl
  have := hc
  have := completedPush_preservesKInjective l (diagonalImmersion Y)
  have : PreservesFiniteLimits
      (diagonalTracePush l (diagonalImmersion Y) ⋙ diagonalTracePush l f) :=
    preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits
      (diagonalTracePush l (diagonalImmersion Y) ⋙ diagonalTracePush l f) :=
    preservesFiniteColimits_of_natIso e.symm
  have : CategoryTheory.Abelian.HasKInjectiveResolutions
      (DiagonalCompleted l (ProjectiveLine Y)) :=
    Scheme.proEtaleRingModules_hasKInjectiveResolutions (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)
  exact rightSingle_isIso_on_exact_image (diagonalTracePush l (diagonalImmersion Y))
    (diagonalTracePush l f) R (SheafOfModules.unit (Scheme.purTwistRing (ProjectiveLine Y)
      (Scheme.purTwistZlCompletion (ProjectiveLine Y) l)))

attribute [local irreducible] diagonalTracePush supportedIso

/-- The ordinary diagonal source comparison is available for either projection.

Source: diagonal tower trace proof paragraph (2), construction step 9
(blueprint: lem-sfb-diagonal-trace-supported-source-existence).
Proof: compose the closed diagonal pushforward with the chosen projection. The
identity of the diagonal followed by that projection gives the ordinary source
comparison, with its additive normalization verified on sections. Ringed closed
pushforward and scalar restriction are exact; identified-coefficient inverse image is
exact, so its right adjoint preserves K-injectives. Resolve the coefficient unit before
pushing along the diagonal. Naturality of the derived unit, its computation on the
resulting K-injective complex, and exactness of the composite (naturally the identity)
prove the required acyclicity. These data assemble the prescribed `SupportedSource`.
-/
theorem diagonalTrace_supportedSource_exists
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (hf : f = pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ∨
      f = pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (t : Result l (ULift.{u} (Padic l)) f) :
    Nonempty (SupportedSource l Y f t.Rc) := by
  have h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y) := by
    rcases hf with rfl | rfl
    · exact pullback.diagonal_fst _
    · exact pullback.diagonal_snd _
  obtain ⟨e, he⟩ := completedPush_section l (diagonalImmersion Y) f h
  exact ⟨⟨h, supportedIso l Y f e, supportedIso_normalization l Y f h e he,
    supported_acyclic l Y f t.Rc e⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
