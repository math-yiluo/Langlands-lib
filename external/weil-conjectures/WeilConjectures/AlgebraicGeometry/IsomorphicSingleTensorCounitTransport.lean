/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.PinnedSingleTensorShifts
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
/-! # Canonical transport under an isomorphic source
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-transport). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Derived universal-property comparisons must identify the sheaf-module category instances.
/-- The canonical transport isomorphism for an isomorphic source.
Source: Stacks Project, Tags 08HY, 0096 and 0D5S.
(blueprint: lem-pc-isomorphic-single-tensor-counit-transport).
Proof: tensor pullback along the isomorphism is an equivalence, and its
selected derived adjunction transports the single-complex functor. More precisely,
the inverse components are the derived adjunction unit on (p^*M)[0], followed
by direct image of the pinned single tensor comparison for e and the single
complex image of the canonical underived composition comparison b. Each
factor is natural. Since e is an isomorphism, tensor pullback is an exact
equivalence, so its derived unit and single comparison are invertible;
b is invertible as well. These component maps therefore form a natural
isomorphism whose inverse is t. The displayed inverse components determine
t uniquely. This also works for zero modules and empty schemes. -/
theorem exists_isomorphic_single_tensor_counit_transport
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X P Z : Scheme.{u}} (p : P ⟶ X) (e : Z ≅ P) :
    let a := Classical.choose (exists_schemeDerivedAdjunction e.hom
      (hAdd := (Classical.choose exists_derivedPullbackComposition) e.hom)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) e.hom)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) e.hom))
    let b := (conjugateIsoEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (e.hom ≫ p)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction e.hom)))).symm
          (Scheme.Modules.pushforwardComp e.hom p).symm
    ∃ t : (Scheme.Modules.tensorPullback (e.hom ≫ p) ⋙
      DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0) ⋙
      schemeDerivedDirectImage e.hom ≅
      Scheme.Modules.tensorPullback p ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0,
      ∀ M : X.Modules,
        t.inv.app M =
          a.unit.app ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback p).obj M)) ≫
          (schemeDerivedDirectImage e.hom).map
            (pinnedSingleTensorCounit e.hom 0 ((Scheme.Modules.tensorPullback p).obj M) ≫
              (DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).map (b.hom.app M))
      := by
  classical
  dsimp only
  let a := Classical.choose (exists_schemeDerivedAdjunction e.hom
      (hAdd := (Classical.choose exists_derivedPullbackComposition) e.hom)
      ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) e.hom)
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) e.hom))
  let b := (conjugateIsoEquiv
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (e.hom ≫ p)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction e.hom)))).symm
          (Scheme.Modules.pushforwardComp e.hom p).symm
  let : HasDerivedCategory.{w} P.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toRingedSpace)))
  let : HasDerivedCategory.{w} Z.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace)))
  let T := Scheme.Modules.tensorPullback e.hom
  have : T.IsEquivalence := by
    obtain ⟨c₁⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.inv e.hom
    obtain ⟨c₂⟩ := Scheme.Modules.nonempty_tensorPullbackComp e.hom e.inv
    obtain ⟨u₁⟩ := Scheme.Modules.nonempty_tensorPullbackId P
    obtain ⟨u₂⟩ := Scheme.Modules.nonempty_tensorPullbackId Z
    let d₁ := c₁.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback e.inv_hom_id) ≪≫ u₁
    let d₂ := c₂.symm ≪≫
      eqToIso (congrArg Scheme.Modules.tensorPullback e.hom_inv_id) ≪≫ u₂
    exact (CategoryTheory.Equivalence.mk T (Scheme.Modules.tensorPullback e.inv)
      d₁.symm d₂).isEquivalence_functor
  let ε := pinnedPullbackCounit.{u, w} e.hom
  let W := HomotopyCategory.quasiIso P.Modules (.up ℤ)
  have : (DerivedCategory.Qh (C := P.Modules)).IsLocalization W :=
    inferInstanceAs ((DerivedCategory.Qh (C := P.Modules)).IsLocalization
      (HomotopyCategory.quasiIso P.Modules (.up ℤ)))
  have : (derivedPullback e.hom).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) e.hom
  have hInv : W.IsInvertedBy (T.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W T.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh W) T.mapDerivedCategory
  have : IsIso ε :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback e.hom) ε hInv
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W T.mapDerivedCategory T.mapDerivedCategoryFactorsh
  let compute := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback e.hom)
    ε T.mapDerivedCategoryFactorsh.hom W
  have : (derivedPullback e.hom).IsEquivalence :=
    Functor.isEquivalence_of_iso compute.symm
  have : (schemeDerivedDirectImage e.hom).IsEquivalence :=
    a.isEquivalence_right_of_isEquivalence_left
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0
  let S' := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0
  let γ : S ⋙ derivedPullback e.hom ⟶ T ⋙ S' :=
    Functor.whiskerLeft (HomotopyCategory.singleFunctor _ 0) ε ≫
      Functor.whiskerRight
        ((SingleFunctors.mappedHomotopySingleIso T).hom.hom 0) DerivedCategory.Qh
  have hγ (G : P.Modules) : γ.app G = pinnedSingleTensorCounit e.hom 0 G := by
    dsimp only [γ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [SingleFunctors.mappedHomotopySingleIso_hom_app]
    rfl
  have : IsIso γ := by dsimp only [γ]; infer_instance
  let τ : Scheme.Modules.tensorPullback p ⋙ S ⟶
      (Scheme.Modules.tensorPullback (e.hom ≫ p) ⋙ S') ⋙
        schemeDerivedDirectImage e.hom :=
    Functor.whiskerLeft (Scheme.Modules.tensorPullback p ⋙ S) a.unit ≫
      Functor.whiskerRight (Functor.whiskerLeft (Scheme.Modules.tensorPullback p) γ)
        (schemeDerivedDirectImage e.hom) ≫
      Functor.whiskerRight (Functor.whiskerRight b.hom S') (schemeDerivedDirectImage e.hom)
  have : IsIso τ := by dsimp only [τ]; infer_instance
  refine ⟨(asIso τ).symm, ?_⟩
  intro M
  change τ.app M = _
  simp only [τ, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    hγ, Functor.map_comp]
  rfl
end AlgebraicGeometry
