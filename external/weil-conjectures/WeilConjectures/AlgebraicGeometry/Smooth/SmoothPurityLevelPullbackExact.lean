/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

set_option linter.privateModule false

/-! # Ordinary coefficient-tower inverse-image ingredients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {T S : Scheme.{t}} (g : T ⟶ S)

open CategoryTheory.Functor.sheafPullbackConstruction

private abbrev site (X : Scheme.{t}) := Scheme.coefficientProEtaleSiteModel.{t, u} X
private abbrev top (X : Scheme.{t}) := Scheme.coefficientProEtaleModelTopology.{t, u} X
private abbrev base := Scheme.coefficientProEtaleModelBaseChange.{t, u} g

private def ringEquiv (X : Scheme.{t}) :
    Sheaf (top.{t, u} X) CommRingCat.{max u (t + 1)} ≌
      Sheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)} :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ site.{t, u} X).sheafPushforwardContinuous _
      (Scheme.ProEt.topology X) (top.{t, u} X))
    ((AsSmall.down : site.{t, u} X ⥤ X.ProEt).sheafPushforwardContinuous _
      (top.{t, u} X) (Scheme.ProEt.topology X)) (Iso.refl _) (Iso.refl _)

private instance ringColimits :
    HasColimitsOfSize.{t, t + 1} CommRingCat.{max u (t + 1)} :=
  hasColimitsOfSizeShrink.{t, t + 1, max u (t + 1), max u (t + 1)} _

private abbrev originalPull := sheafPullback (Scheme.proEtaleBaseChange g)
  CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)
private abbrev originalAdj := sheafAdjunctionContinuous (Scheme.proEtaleBaseChange g)
  CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T)

private def ringMap (A : CommRingCat.{max u (t + 1)}) :=
  Scheme.coefficientProEtaleDirectRingMap.{t, u} g A

private theorem comparison_iso (A : CommRingCat.{max u (t + 1)}) :
    IsIso (((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A)) := by
  let U : S.ProEt := Scheme.ProEt.mk (𝟙 S)
  let hU : IsTerminal U := MorphismProperty.Over.mkIdTerminal _ S
  let hV : IsTerminal ((Scheme.proEtaleBaseChange g).obj U) :=
    hU.isTerminalObj (Scheme.proEtaleBaseChange g)
  let eR : (Scheme.proEtaleBaseChange g).sheafPushforwardContinuous
      CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology S) (Scheme.ProEt.topology T) ⋙
      (sheafSections _ _).obj (op U) ≅
        (sheafSections _ _).obj (op ((Scheme.proEtaleBaseChange g).obj U)) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _)
  let a := ((constantSheafAdj (Scheme.ProEt.topology S)
    CommRingCat.{max u (t + 1)} hU).comp (originalAdj.{t, u} g)).ofNatIsoRight eR
  let b := constantSheafAdj (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} hV
  let e := a.leftAdjointUniq b
  have he : ((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A) =
      e.hom.app A := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [a, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    simp only [eR,
      NatIso.ofComponents_hom_app, Iso.refl_hom]
    change (constantSheafAdj (Scheme.ProEt.topology S) _ hU).homEquiv _ _
      ((originalAdj.{t, u} g).homEquiv _ _
        (((originalAdj.{t, u} g).homEquiv _ _).symm (ringMap.{t, u} g A)))
        ≫ 𝟙 _ = _
    rw [Equiv.apply_symm_apply, Category.comp_id]
    change (constantSheafAdj (Scheme.ProEt.topology S) _ hU).homEquiv _ _
      (ringMap.{t, u} g A) = b.unit.app A
    unfold ringMap Scheme.coefficientProEtaleDirectRingMap
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{max u (t + 1)} hU).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{max u (t + 1)}).homEquiv _ _
        (((sheafificationAdjunction (Scheme.ProEt.topology S)
          CommRingCat.{max u (t + 1)}).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    simp only [b, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj_unit_app, Category.id_comp, sheafificationAdjunction_unit_app]
    rfl
  rw [he]
  infer_instance

@[irreducible] private def modelAdj :
    (ringEquiv.{t, u} S).functor ⋙ originalPull.{t, u} g ⋙
      (ringEquiv.{t, u} T).inverse ⊣
      (base.{t, u} g).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (top.{t, u} S) (top.{t, u} T) :=
  (originalAdj.{t, u} g).restrictFullyFaithful
    (ringEquiv.{t, u} S).fullyFaithfulFunctor (ringEquiv.{t, u} T).fullyFaithfulFunctor
    (Iso.refl _) (Iso.refl _)

private abbrev constantRing (X : Scheme.{t}) (A : CommRingCat.{max u (t + 1)}) :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.ProEtale
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
