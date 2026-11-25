/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti

import WeilConjectures.AlgebraicGeometry.RelativelyFlatCanonicalModuleBaseChange
import WeilConjectures.AlgebraicGeometry.PicardH1BaseDescentFibreGenerator
import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Degree-zero fibre cohomology of a descended line bundle

## References

* Stacks Project, Tag 0BF2, the displayed fibre comparison
* Tags 0BF0 and 0B91(2)
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyFree_isFlatOver {X S : Scheme.{v}}
    (f : X ⟶ S) [Flat f] (G : X.Modules) [G.IsFiniteLocallyFree] :
    G.IsFlatOver f := by
  intro V U e
  let := (f.appLE V.1 U.1 e).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(X, U.1) :=
    HasRingHomProperty.appLE @Flat f ‹_› V U e
  have := (Modules.finitePresentation_projective_sections G U.2).2
  let : Module Γ(S, V.1) Γ(G, U.1) := Module.compHom _ (f.appLE V.1 U.1 e).hom
  have : IsScalarTower Γ(S, V.1) Γ(X, U.1) Γ(G, U.1) :=
    ⟨fun a b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(S, V.1) Γ(X, U.1) Γ(G, U.1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_iso_of_generatesAt {Y : Scheme.{v}} (M : Y.Modules)
    (τ : Γ(M, ⊤)) (hτ : ∀ y : Y, Modules.GeneratesAt τ y) :
    Nonempty (M ≅ SheafOfModules.unit Y.ringCatSheaf) := by
  have htop : Modules.generatingLocus τ = ⊤ := eq_top_iff.mpr (fun y _ ↦ hτ y)
  have he := Modules.isFreeGenerator_generatingLocus τ
  rw [htop] at he
  have he' : Modules.IsFreeGenerator τ := by simpa using he
  let e := Modules.pullbackIotaUnitIsoOfOverIso he'.overIso
  exact ⟨((Modules.pullbackId Y).app M).symm ≪≫
    (Modules.pullbackCongr (Scheme.toIso_inv_ι Y).symm).app M ≪≫
    (Modules.pullbackComp _ _).symm.app M ≪≫
    (Modules.pullback Y.topIso.inv).mapIso e ≪≫ Modules.pullbackObjUnitIso _⟩

private theorem appTop_isIso_of_tensor_unit {A B : Scheme.{v}} (a : A ⟶ B)
    (h : IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).unit.app
      (SheafOfModules.unit B.ringCatSheaf))) : IsIso a.appTop := by
  have := h
  have := (Modules.tensorPullbackObjUnitToUnit_isIso a).1
  have hs : IsIso (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom) := by
    rw [← (Modules.tensorPullbackObjUnitToUnit_isIso a).2]
    infer_instance
  have happ := Functor.map_isIso (SheafOfModules.evaluation B.ringCatSheaf
    (Opposite.op ⊤)) (SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom)
  rw [ConcreteCategory.isIso_iff_bijective] at happ ⊢
  exact happ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero residue cohomology of a descended line bundle is the residue field. -/
theorem picard_directImage_fibre_cohomology_zero
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (hO : ∀ {T : Scheme.{v}} (g : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (L : X.Modules) [L.IsInvertible]
    (W : Scheme.{v}) (k : W ⟶ S) [IsImmersion k]
    (w : W) (s : S) (hw : k w = s)
    (hLs : ∃ (N : (Spec (S.residueField s)).Modules) (_ : N.IsFiniteLocallyFree),
      Nonempty ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj L ≅
        (Modules.tensorPullback (pullback.snd f (S.fromSpecResidueField s))).obj N)) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    Nonempty (derivedFiberCohomology W E 0 w ≅
      ModuleCat.of (W.residueField w) (W.residueField w)) := by
  classical
  dsimp only
  let : ∀ U : W.Opens, HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) :=
    fun U ↦ HasDerivedCategory.standard _
  let : ∀ {Y Z : Scheme.{v}} (a : Y ⟶ Z), (Modules.tensorPullback a).Additive := by
    intro Y Z a
    let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction a)
    let : (Modules.tensorPullback a).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
    exact CategoryTheory.rightExactFunctor_le_additiveFunctor _ _ _ (by
      rw [CategoryTheory.rightExactFunctor_iff]
      infer_instance)
  let fW := pullback.snd f k
  let G := (Modules.tensorPullback (pullback.fst f k)).obj L
  let eG : G ≅ (Modules.pullback (pullback.fst f k)).obj L :=
    ((Classical.choose (Modules.exists_tensorPullbackAdjunction (pullback.fst f k))).leftAdjointUniq
       (Modules.pullbackPushforwardAdjunction (pullback.fst f k))).app L
  have : G.IsInvertible := Modules.IsInvertible.of_iso eG.symm
  have : SheafOfModules.IsInvertible.{v, v, v} G :=
    Modules.IsInvertible.sheafOfModules_isInvertible G
  have hflat : G.IsFlatOver fW := finiteLocallyFree_isFlatOver fW G
  let g := W.fromSpecResidueField w
  let p := pullback.fst fW g
  let q := pullback.snd fW g
  obtain ⟨c, hc, hiso⟩ := exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    fW g p q (IsPullback.of_hasPullback fW g) G hflat
  let φ := schemeDerivedBaseChangeMap fW q g p pullback.condition
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj G) ≫
    (schemeDerivedDirectImage q).map c
  have : IsIso φ := hiso
  let b := pullbackLeftPullbackSndIso f k g
  let gw := g ≫ k
  obtain ⟨τ, hτ⟩ := picard_h1_base_descent_fibre_generator f hO L W k w s hw hLs
  obtain ⟨eτ⟩ := unit_iso_of_generatesAt _ τ hτ
  obtain ⟨c₁⟩ := Modules.nonempty_tensorPullbackComp p (pullback.fst f k)
  obtain ⟨c₂⟩ := Modules.nonempty_tensorPullbackComp b.hom (pullback.fst f gw)
  have hb : b.hom ≫ pullback.fst f gw = p ≫ pullback.fst f k :=
    pullbackLeftPullbackSndIso_hom_fst f k g
  let d : (Modules.tensorPullback (p ≫ pullback.fst f k)).obj L ≅
      (Modules.tensorPullback (b.hom ≫ pullback.fst f gw)).obj L :=
    eqToIso (congrArg (fun a ↦ (Modules.tensorPullback a).obj L) hb.symm)
  let cb := (Modules.nonempty_tensorPullbackAdjunction b.hom).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction b.hom)
  let eF : (Modules.tensorPullback p).obj G ≅
      SheafOfModules.unit (pullback fW g).ringCatSheaf :=
    c₁.symm.app L ≪≫ d ≪≫ c₂.app L ≪≫
      (Modules.tensorPullback b.hom).mapIso eτ ≪≫ cb.app _ ≪≫ Modules.pullbackObjUnitIso _
  have hq : IsIso q.appTop := by
    have : IsIso (pullback.snd f gw).appTop := appTop_isIso_of_tensor_unit _ (hO gw)
    have hbq : b.hom ≫ pullback.snd f gw = q :=
      pullbackLeftPullbackSndIso_hom_snd f k g
    rw [← hbq, Hom.comp_appTop]
    infer_instance
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings (Spec (W.residueField w)).toRingedSpace)) 0
  let P := RingedSpace.moduleDirectImage q.toLRSHom.toShHom
  have : PreservesFiniteLimits P := by
    change PreservesFiniteLimits (Modules.pushforward q)
    infer_instance
  let e := H.mapIso (asIso φ) ≪≫
    P.homologyRightDerivedFunctorObjSingleFunctorIso ((Modules.tensorPullback p).obj G) 0 ≪≫
    P.rightDerivedZeroIsoSelf.app ((Modules.tensorPullback p).obj G) ≪≫ P.mapIso eF
  let R := ModuleCat.restrictScalars (ΓSpecIso (W.residueField w)).inv.hom
  let Γ := SheafOfModules.evaluation
    (moduleRings (Spec (W.residueField w)).toRingedSpace) (Opposite.op ⊤)
  let eΓ : Γ.obj (P.obj (SheafOfModules.unit (pullback fW g).ringCatSheaf)) ≅
      ModuleCat.of Γ(Spec (W.residueField w), ⊤) Γ(Spec (W.residueField w), ⊤) :=
    ModuleCat.restrictScalarsIsoOfEquiv (asIso q.appTop).commRingCatIsoToRingEquiv
  exact ⟨(Γ ⋙ R).mapIso e ≪≫ R.mapIso eΓ ≪≫
    ModuleCat.restrictScalarsIsoOfEquiv
      (ΓSpecIso (W.residueField w)).symm.commRingCatIsoToRingEquiv⟩

end AlgebraicGeometry.Scheme
