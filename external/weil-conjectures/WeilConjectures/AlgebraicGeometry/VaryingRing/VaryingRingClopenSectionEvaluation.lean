/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingClopenArrowFactors
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinarySectionEvaluation
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryClopenProjectorEvaluation
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOrdinaryOpenUnit
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.MateEvaluationScalars.TowerMateEvaluationScalars
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-!
# Coefficient realization of the clopen section factor

Source: the clopen construction in Stacks 0F7B and Zheng, Construction 4.1.
The comparison concerns the clopen projector and its outgoing composition identifications.
(blueprint: lem-sp-varying-ring-clopen-section-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.VaryingRing
variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

attribute [local instance 2000] WeilConjectures.SemilinearSections.sequenceSmall
  StrictTower.towers_hasDerivedCategory Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor ordinaryRealization moduleEvalG moduleGComp
  StrictTower.moduleGComp ordinaryOpenEvaluation

-- Adjunction pasting elaborates several chosen adjoints and their comparison cells.
private theorem moduleOpen_composition (n : ℕ) {U V X : Scheme.{u}}
    (i : U ⟶ V) (j : V ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] :
    OpenComparisonComposition (ordinaryOpenEvaluation R φ n i)
      (ordinaryOpenEvaluation R φ n j) (ordinaryOpenEvaluation R φ n (i ≫ j))
      (moduleJComp R φ i j) (StrictTower.openBetaModuleJComp (R n) i j) := by
  apply open_from_inverse_pasting
  apply mateSquare ((moduleJAdj R φ i).comp (moduleJAdj R φ j))
    (moduleJAdj R φ (i ≫ j))
    ((StrictTower.moduleJAdj (R n) i).comp (StrictTower.moduleJAdj (R n) j))
    (StrictTower.moduleJAdj (R n) (i ≫ j))
  rw [mateEquiv_hcomp, ordinaryOpenEvaluation_mate, ordinaryOpenEvaluation_mate,
    ordinaryOpenEvaluation_mate, module_conj]
  have hc : conjugateEquiv
      ((StrictTower.moduleJAdj (R n) i).comp (StrictTower.moduleJAdj (R n) j))
      (StrictTower.moduleJAdj (R n) (i ≫ j))
      (StrictTower.openBetaModuleJComp (R n) i j).inv =
        (StrictTower.moduleGComp (R n) i j).inv := by
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv
      (StrictTower.moduleJAdj (R n) i) (StrictTower.moduleJAdj (R n) j)
      (StrictTower.moduleJAdj (R n) (i ≫ j)) (StrictTower.moduleGComp (R n) i j).symm
  rw [hc]
  have hp : ComparisonComposition (moduleEvalG R φ j n) (moduleEvalG R φ i n)
      (moduleEvalG R φ (i ≫ j) n) (moduleGComp R φ i j)
      (StrictTower.moduleGComp (R n) i j) := ordinaryModuleEvalG_comp R φ n i j
  exact pull_mate_pasting (moduleEvalG R φ i n) (moduleEvalG R φ j n)
    (moduleEvalG R φ (i ≫ j) n) (moduleGComp R φ i j)
    (StrictTower.moduleGComp (R n) i j) hp

-- The comparison types contain several chosen adjoints.
private theorem moduleOpen_tail (n : ℕ) {U V X : Scheme.{u}}
    (s : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion k]
    (hk : s ≫ b = k) :
    openCompatible (ordinaryOpenEvaluation R φ n s) (ordinaryOpenEvaluation R φ n b)
      (ordinaryOpenEvaluation R φ n k)
      (moduleJComp R φ s b ≪≫ moduleJCongr R φ hk)
      (StrictTower.openBetaModuleJComp (R n) s b ≪≫ StrictTower.singleJCongr (R n) hk) := by
  subst k
  intro M
  simpa only [Iso.trans_hom, NatTrans.comp_app, moduleJCongr, moduleJ_congr,
    eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id,
    StrictTower.singleJCongr_refl] using moduleOpen_composition R φ n s b M

private theorem modulePull_tail (n : ℕ) {V P S : Scheme.{u}}
    (s : V ⟶ P) (q : P ⟶ S) (r : V ⟶ S) (hr : s ≫ q = r) :
    pullCompatible (moduleEvalG R φ s n) (moduleEvalG R φ q n)
      (moduleEvalG R φ r n)
      ((eqToIso (congrArg (pull R φ) hr)).symm ≪≫ moduleGComp R φ s q)
      ((eqToIso (congrArg (StrictTower.modulePullback (R n)) hr)).symm ≪≫
        StrictTower.moduleGComp (R n) s q) := by
  subst r
  simpa only [pullCompatible, eqToIso_refl, Iso.refl_symm, Iso.refl_trans] using
    ordinaryModuleEvalG_comp R φ n s q

private theorem moduleProjector (n : ℕ) {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] (M : Modules R φ X) :
    (eval R φ X n).map ((modulePi R φ s).app M) ≫
        (ordinaryOpenEvaluation R φ n s).hom.app ((pull R φ s).obj M) ≫
        (StrictTower.moduleJ (R n) s).map ((moduleEvalG R φ s n).hom.app M) =
      (StrictTower.clopenModulePi (R n) s).app ((eval R φ X n).obj M) := by
  let O : X.Opens :=
    ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hπ := (StrictTower.clopenModule_section_projector (R n) s O.ι
    (Scheme.Opens.range_ι O)).2.1
  have ht := StrictTower.clopenModuleToDirect_isIso (R n) s
  exact projector_comparison (moduleJAdj R φ s) (StrictTower.moduleJAdj (R n) s)
    (StrictTower.clopenModuleAdj (R n) s)
    (asIso (StrictTower.clopenModuleToDirect (R n) s))
    (moduleEvalG R φ s n) (ordinaryOpenEvaluation R φ n s)
    (modulePi R φ s) (StrictTower.clopenModulePi (R n) s)
    (modulePi_image R φ s) hπ
    (unit_comparison (moduleJAdj R φ s) (StrictTower.moduleJAdj (R n) s)
      (moduleEvalG R φ s n) (ordinaryOpenEvaluation R φ n s)
      (ordinaryOpenEvaluation_mate R φ n s)) M

private def singleSection (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    StrictTower.modulePullback B (pullback.snd p i) ⋙
        StrictTower.moduleJ B (pullback.fst p i) ⟶
      StrictTower.modulePullback B r ⋙ StrictTower.moduleJ B k :=
  Functor.whiskerRight (Functor.whiskerLeft (StrictTower.modulePullback B (pullback.snd p i))
    (StrictTower.clopenModulePi B (StrictTower.squareLift k r p i h)))
      (StrictTower.moduleJ B (pullback.fst p i)) ≫
    Functor.whiskerRight
      (Functor.associator (StrictTower.modulePullback B (pullback.snd p i))
        (StrictTower.modulePullback B (StrictTower.squareLift k r p i h))
        (StrictTower.moduleJ B (StrictTower.squareLift k r p i h))).inv
      (StrictTower.moduleJ B (pullback.fst p i)) ≫
    (Functor.associator
      (StrictTower.modulePullback B (pullback.snd p i) ⋙
        StrictTower.modulePullback B (StrictTower.squareLift k r p i h))
      (StrictTower.moduleJ B (StrictTower.squareLift k r p i h))
      (StrictTower.moduleJ B (pullback.fst p i))).hom ≫
    Functor.whiskerLeft
      (StrictTower.modulePullback B (pullback.snd p i) ⋙
        StrictTower.modulePullback B (StrictTower.squareLift k r p i h))
      ((StrictTower.openBetaModuleJComp B (StrictTower.squareLift k r p i h)
        (pullback.fst p i)).hom ≫ (StrictTower.singleJCongr B (pullback.lift_fst k r h)).hom) ≫
    Functor.whiskerRight
      ((StrictTower.moduleGComp B (StrictTower.squareLift k r p i h)
        (pullback.snd p i)).inv ≫
        (eqToIso (congrArg (StrictTower.modulePullback B) (pullback.lift_snd k r h))).hom)
      (StrictTower.moduleJ B k)

-- Elaborate the six comparison cells without unfolding their chosen adjoints.
private theorem moduleSection_comparison (n : ℕ) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    OrdinarySquareComparison (moduleEvalG R φ r n)
      (ordinaryOpenEvaluation R φ n (pullback.fst p i))
      (ordinaryOpenEvaluation R φ n k) (moduleEvalG R φ (pullback.snd p i) n)
      (moduleSectionArrow R φ k r p i h) (singleSection (R n) k r p i h) := by
  let s := StrictTower.squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  have hs : IsOpenImmersion s := StrictTower.squareLift_open k r p i h
  have hc : IsClosedImmersion s := StrictTower.squareLift_closed k r p i h
  simpa only [moduleSectionArrow, singleSection, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_inv, s, b, q] using section_comparison
    (moduleEvalG R φ s n) (ordinaryOpenEvaluation R φ n s)
    (ordinaryOpenEvaluation R φ n b) (moduleEvalG R φ q n)
    (ordinaryOpenEvaluation R φ n k) (moduleEvalG R φ r n)
    (moduleJComp R φ s b ≪≫ moduleJCongr R φ (pullback.lift_fst k r h))
    (StrictTower.openBetaModuleJComp (R n) s b ≪≫
      StrictTower.singleJCongr (R n) (pullback.lift_fst k r h))
    ((eqToIso (congrArg (pull R φ) (pullback.lift_snd k r h))).symm ≪≫
      moduleGComp R φ s q)
    ((eqToIso (congrArg (StrictTower.modulePullback (R n))
      (pullback.lift_snd k r h))).symm ≪≫ StrictTower.moduleGComp (R n) s q)
    (modulePi R φ s) (StrictTower.clopenModulePi (R n) s)
    (moduleOpen_tail R φ n s b k (pullback.lift_fst k r h))
    (modulePull_tail R φ n s q r (pullback.lift_snd k r h))
    (moduleProjector R φ n s)

private theorem evalJ_ordinary (n : ℕ) {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    evalJ R φ j n = Functor.mapDerivedCategorySquareIso (ordinaryOpenEvaluation R φ n j) := by
  rw [ordinaryOpenEvaluation_inverse, evalJ_inverse_localized]
  apply Iso.ext
  exact (Functor.square_symm_hom _).symm

attribute [local instance] StrictTower.clopenTowerAbelian
attribute [local semireducible] Functor.mapDerivedCategory

set_option backward.defeqAttrib.useBackward true in
private theorem strictSection_descent (B : Type (u + 1)) [CommRing B]
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    StrictTower.ClopenProjectorDescent
      (aA := StrictTower.clopenTowerAbelian B S)
      (aD := StrictTower.clopenTowerAbelian B W)
      (StrictTower.towerPullback B (pullback.snd p i) ⋙
        StrictTower.towerJ B (pullback.fst p i))
      (StrictTower.towerPullback B r ⋙ StrictTower.towerJ B k)
      (Functor.termwiseCompositeTransformation _ _ _ _ _ _ _ _ _
        (singleSection B k r p i h))
      ((Functor.mapDerivedCategoryCompIso
        (StrictTower.towerPullback B (pullback.snd p i))
        (StrictTower.towerJ B (pullback.fst p i))).inv ≫
        strictSectionArrow B k r p i h ≫
        (Functor.mapDerivedCategoryCompIso (StrictTower.towerPullback B r)
          (StrictTower.towerJ B k)).hom) := by
  let q := pullback.snd p i
  let b := pullback.fst p i
  let s := StrictTower.squareLift k r p i h
  obtain ⟨C, c, hc, hc'⟩ := (StrictTower.properOpen_clopen_geometry k r p i h).2.2.2.2
  let : IsOpenImmersion c := hc
  have hd := StrictTower.module_localization_paste
    (aA := StrictTower.ordinaryAbelian B S)
    (aD := StrictTower.ordinaryAbelian B (pullback p i))
    (aE := StrictTower.ordinaryAbelian B W) (aC := StrictTower.ordinaryAbelian B V)
    (aT := StrictTower.ordinaryAbelian B (pullback p i))
    (hA := StrictTower.towers_hasDerivedCategory B S)
    (hD := StrictTower.towers_hasDerivedCategory B (pullback p i))
    (hE := StrictTower.towers_hasDerivedCategory B W)
    (hC := StrictTower.towers_hasDerivedCategory B V)
    (hT := StrictTower.towers_hasDerivedCategory B (pullback p i))
    (StrictTower.modulePullback B q) (StrictTower.moduleJ B b)
    (StrictTower.modulePullback B q) (StrictTower.modulePullback B s)
    (StrictTower.moduleJ B s) (StrictTower.moduleJ B b)
    (StrictTower.moduleJ B k) (StrictTower.modulePullback B r)
    (𝟙 _) (StrictTower.clopenModulePi B s)
    ((StrictTower.openBetaModuleJComp B s b).hom ≫
      (StrictTower.singleJCongr B (pullback.lift_fst k r h)).hom)
    ((StrictTower.moduleGComp B s q).inv ≫
      (eqToIso (congrArg (StrictTower.modulePullback B) (pullback.lift_snd k r h))).hom)
    (𝟙 _) (StrictTower.pi B s)
    ((StrictTower.jComp B s b).hom ≫ (StrictTower.jCongr B (pullback.lift_fst k r h)).hom)
    ((StrictTower.gComp B s q).inv ≫
      (eqToIso (congrArg (StrictTower.G B) (pullback.lift_snd k r h))).hom)
    (by
      have ht : Functor.termwiseCompositeTransformation ℕᵒᵖ
          (StrictTower.Modules B S) (StrictTower.Modules B (pullback p i))
          (StrictTower.Modules B (pullback p i)) (StrictTower.Modules B W)
          (StrictTower.modulePullback B q) (StrictTower.moduleJ B b)
          (StrictTower.modulePullback B q) (StrictTower.moduleJ B b) (𝟙 _) = 𝟙 _ := by
        unfold Functor.termwiseCompositeTransformation
        rw [CategoryTheory.Functor.map_id]
        rw [Category.id_comp, Iso.hom_inv_id]
      rw [ht]
      intro K
      simp only [NatTrans.id_app, Category.id_comp, NatTrans.mapHomologicalComplex_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id])
    (StrictTower.pi_fac B s c hc')
    (StrictTower.jTail_fac B s b k (pullback.lift_fst k r h))
    (StrictTower.gTail_fac B s q r (pullback.lift_snd k r h))
  simpa only [singleSection, strictSectionArrow, Category.id_comp,
    StrictTower.G, StrictTower.J, StrictTower.tw, StrictTower.towerPullback,
    StrictTower.towerJ, StrictTower.clopenTowerAbelian, StrictTower.ordinaryAbelian] using hd

/-- Coefficient evaluation preserves the clopen section projection and its
outgoing composition identifications.
Source: Stacks 0F7B, open case, and 09AE; Zheng, Construction 4.1
(blueprint: lem-sp-varying-ring-clopen-section-evaluation).
Proof: put q = pullback.snd p i, b = pullback.fst p i and s = squareLift k r p i h.
The lift s is open and closed. In the ordinary module category the normalized
map pi_s restricts to the open-adjunction unit on its image and to zero on the
complement. The clopen sheaf product decomposition therefore determines it.
Module evaluation preserves these two restrictions and the unit. Consequently
it gives the single-coefficient clopen projection, and strict-tower evaluation
gives the same map termwise. Compose with b_!, then use the specified
identifications b_! s_! = k_! and s^* q^* = r^*. Coefficient evaluation preserves
the pullback compositor by the unit-normalized pull/direct mate calculation;
it preserves the open compositor by taking open-adjunction mates. Equality
transport is proof-irrelevant. These equations identify both evaluated section
factors with the single-coefficient one. Carry out the varying-system argument
on complexes and apply Q, since sectionArrow is the exact localization of the
ordinary section factor. For strict towers, the derived units and the inverse
open-to-direct comparison localize the same ordinary clopen projection. The
localization factor isomorphisms and essential surjectivity extend the equations
to arbitrary derived inputs. No cartesian open base-change comparison enters
this factor, and no equality of arbitrary derived maps is detected by evaluation. -/
theorem clopenSectionEvaluation {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) (n : ℕ) :
    ∃ a : (StrictTower.modulePullback (R n) (pullback.snd p i)).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory ⟶
        (StrictTower.modulePullback (R n) r).mapDerivedCategory ⋙
          (StrictTower.moduleJ (R n) k).mapDerivedCategory,
      (∀ N : Derived R φ S,
        (ev R φ W n).map ((sectionArrow R φ k r p i h).app N) ≫
            (evalJ R φ k n).hom.app ((G R φ r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((evalG R φ r n).hom.app N) =
          (evalJ R φ (pullback.fst p i) n).hom.app
              ((G R φ (pullback.snd p i)).obj N) ≫
            (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory.map
              ((evalG R φ (pullback.snd p i) n).hom.app N) ≫ a.app ((ev R φ S n).obj N)) ∧
      (∀ N : StrictTower.Derived (R n) S,
        (StrictTower.ev (R n) W 0).map ((strictSectionArrow (R n) k r p i h).app N) ≫
            (StrictTower.evalJ (R n) k 0).hom.app ((StrictTower.G (R n) r).obj N) ≫
            (StrictTower.moduleJ (R n) k).mapDerivedCategory.map
              ((StrictTower.evalG (R n) r 0).hom.app N) =
          (StrictTower.evalJ (R n) (pullback.fst p i) 0).hom.app
              ((StrictTower.G (R n) (pullback.snd p i)).obj N) ≫
            (StrictTower.moduleJ (R n) (pullback.fst p i)).mapDerivedCategory.map
              ((StrictTower.evalG (R n) (pullback.snd p i) 0).hom.app N) ≫
            a.app ((StrictTower.ev (R n) S 0).obj N)) := by
  let a := localizedArrow
    (StrictTower.modulePullback (R n) (pullback.snd p i))
    (StrictTower.moduleJ (R n) (pullback.fst p i))
    (StrictTower.modulePullback (R n) r) (StrictTower.moduleJ (R n) k)
    (singleSection (R n) k r p i h)
  refine ⟨a, ?_, ?_⟩
  · intro N
    have he := StrictTower.MateEvaluationScalars.exactSquare_scalar
      (eval R φ S n) (eval R φ V n) (eval R φ (pullback p i) n) (eval R φ W n)
      (moduleEvalG R φ r n) (moduleEvalG R φ (pullback.snd p i) n)
      (ordinaryOpenEvaluation R φ n k) (ordinaryOpenEvaluation R φ n (pullback.fst p i))
      (moduleSectionArrow R φ k r p i h) (singleSection (R n) k r p i h)
      (moduleSection_comparison R φ n k r p i h).equation N
    rw [evalJ_ordinary, evalJ_ordinary]
    exact he
  · intro N
    have hd := StrictTower.MateEvaluationScalars.exactSquare_unique
      (StrictTower.towerPullback (R n) (pullback.snd p i))
      (StrictTower.towerJ (R n) (pullback.fst p i))
      (StrictTower.towerPullback (R n) r) (StrictTower.towerJ (R n) k)
      (Functor.termwiseCompositeTransformation _ _ _ _ _ _ _ _ _
        (singleSection (R n) k r p i h)) (strictSectionArrow (R n) k r p i h)
      (strictSection_descent (R n) k r p i h)
    rw [hd, StrictTower.evalJ_eq, StrictTower.evalJ_eq,
      StrictTower.evalG_eq, StrictTower.evalG_eq]
    exact StrictTower.MateEvaluationScalars.evalD_square_trans
      (StrictTower.modulePullback (R n) (pullback.snd p i))
      (StrictTower.moduleJ (R n) (pullback.fst p i))
      (StrictTower.modulePullback (R n) r) (StrictTower.moduleJ (R n) k)
      (singleSection (R n) k r p i h) N 0

end AlgebraicGeometry.ProEtale.VaryingRing
