/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassReduction
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-! The mate calculation used by the integer endpoint square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem sheafification_lift_app
    {C E : Type*} [Category* C] [Category* E]
    (J : GrothendieckTopology C) [HasWeakSheafify J E]
    {P : Cᵒᵖ ⥤ E} (F : Sheaf J E) (t : P ⟶ F.obj) (U : Cᵒᵖ) :
    (toSheafify J P).app U ≫
        (((sheafificationAdjunction J E).homEquiv P F).symm t).hom.app U = t.app U := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction J E).homEquiv P F) t
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U) h

private theorem constant_comparison_mate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J E] [HasWeakSheafify K E]
    (G : C ⥤ D) [G.IsContinuous J K]
    {L : Sheaf J E ⥤ Sheaf K E}
    (adj : L ⊣ G.sheafPushforwardContinuous E J K)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (e : G.sheafPushforwardContinuous E J K ⋙ (sheafSections J E).obj (op T) ≅
      (sheafSections K E).obj (op S)) (a : E)
    (h : (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op (G.obj T)) ≫
      e.hom.app ((constantSheaf K E).obj a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S)) :
    adj.homEquiv _ _
        (((((constantSheafAdj J E hT).comp adj).ofNatIsoRight e).leftAdjointUniq
          (constantSheafAdj K E hS)).hom.app a) =
      ((sheafificationAdjunction J E).homEquiv _ _).symm
        (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) := by
  -- Uniqueness of left adjoints determines the mate by its value on constant sections.
  apply ((constantSheafAdj J E hT).homEquiv _ _).injective
  apply (cancel_mono (e.hom.app ((constantSheaf K E).obj a))).mp
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj J E hT).comp adj).ofNatIsoRight e)
    (constantSheafAdj K E hS) a
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hu
  refine hu.trans ?_
  rw [constantSheafAdj_homEquiv_apply]
  have hs : (constantSheafAdj K E hS).unit.app a =
      (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S) := by
    rw [← Adjunction.homEquiv_id, constantSheafAdj_homEquiv_apply]
    exact Category.comp_id _
  rw [hs]
  have hc := sheafification_lift_app J
    ((G.sheafPushforwardContinuous E J K).obj ((constantSheaf K E).obj a))
    (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) (op T)
  exact h.symm.trans (congrArg (fun k ↦ k ≫ e.hom.app _) hc).symm

private theorem integer_comparison_mate (T : Scheme.{u}) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (integerComparison T).hom =
      ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
          (toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  apply constant_comparison_mate T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) (comparisonAdjunction AddCommGrpCat.{u + 1} T)
    (Scheme.Etale.isTerminalMkId T) (Scheme.ProEt.isTerminalMkId T)
    ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
      (op (Scheme.Etale.mk (𝟙 T))))
  exact Category.comp_id _

private theorem etale_constant_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) =
      ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm (Functor.whiskerLeft f.Etale.op
          (toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  apply constant_comparison_mate Y.smallEtaleTopology X.smallEtaleTopology
    f.Etale (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    terminalIsTerminal terminalIsTerminal
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f)
  change (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app _ ≫
      (sheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map
          (PreservesTerminal.iso f.Etale).inv.op = _
  exact ((toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      (PreservesTerminal.iso f.Etale).inv.op).symm.trans (Category.id_comp _)

/-- The comparison mate for the integer endpoint maps.

Source: Stacks Project, Tag 00WX; this is the adjunction-mate calculation in the
integer endpoint step of the change-of-site construction.
(blueprint: lem-sp-integral-site-pullback-integer-endpoint-mate).

Proof: apply the hom-set adjunctions for the étale and pro-étale inverse images.
The comparison isomorphism is the conjugate of the direct-image comparison, and
`integerComparison` and `upperStarConstantSheafIso` are defined by uniqueness of
left adjoints.  Their defining unit equations reduce both sides to the same
constant-section map. -/
theorem integral_site_pullback_integer_endpoint_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let B := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let AY := (constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let BX := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv A B)
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
        ((comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv B BX
          (integerComparison X).hom) ≫
      (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).symm.hom.app BX =
    (comparisonAdjunction AddCommGrpCat.{u + 1} Y).homEquiv A AY
        (integerComparison Y).hom ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} Y).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv AY BX
          (proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  dsimp only
  have hp : (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
      (proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
    exact Equiv.apply_symm_apply
      ((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) _
  rw [hp, integer_comparison_mate X, integer_comparison_mate Y, etale_constant_mate f]
  -- Compare the extensions from the constant presheaf before sheafification.
  apply ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ _).injective
  simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let ηX := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj Z)
  let ηPX := toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj Z)
  let ηPY := toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj Z)
  let BX := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj Z
  let qX := ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ ((comparisonLowerStar AddCommGrpCat.{u + 1} X).obj BX)).symm
      (Functor.whiskerLeft (Scheme.toProEt X).op ηPX)
  let qp := proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1} Z
  let b := (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).inv.app BX
  change ηX.app (f.Etale.op.obj U) ≫
      (qX.hom.app (f.Etale.op.obj U) ≫ b.hom.app U) =
    ηPY.app ((Scheme.toProEt Y).op.obj U) ≫ qp.hom.app ((Scheme.toProEt Y).op.obj U)
  have hx := sheafification_lift_app X.smallEtaleTopology
    ((comparisonLowerStar AddCommGrpCat.{u + 1} X).obj BX)
    (Functor.whiskerLeft (Scheme.toProEt X).op ηPX) (f.Etale.op.obj U)
  have hy := sheafification_lift_app (Scheme.ProEt.topology Y)
    ((proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj BX)
    (Functor.whiskerLeft (proEtaleBaseChange f).op ηPX) ((Scheme.toProEt Y).op.obj U)
  -- The base-change square is the identity on the underlying fibre product.
  have hb : b.hom.app U = 𝟙 _ := by
    dsimp [b, lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso]
    exact (Category.id_comp _).trans ((Category.comp_id _).trans (BX.obj.map_id _))
  calc
    _ = (ηX.app (f.Etale.op.obj U) ≫ qX.hom.app (f.Etale.op.obj U)) ≫ b.hom.app U :=
      (Category.assoc _ _ _).symm
    _ = ηPX.app ((Scheme.toProEt X).op.obj (f.Etale.op.obj U)) ≫ b.hom.app U :=
      congrArg (fun k ↦ k ≫ b.hom.app U) hx
    _ = ηPX.app ((Scheme.toProEt X).op.obj (f.Etale.op.obj U)) := by
      rw [hb]
      exact Category.comp_id _
    _ = _ := hy.symm

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
