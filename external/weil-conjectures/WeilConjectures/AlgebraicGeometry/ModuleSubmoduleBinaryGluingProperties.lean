/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingCore
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.AlgebraicGeometry.ModuleSubmoduleBinaryGluingSecondRestriction

/-! # The restrictions of the binary submodule pullback

Source: Stacks Project, Properties, Lemma 01PF, binary gluing step.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem isIso_of_components
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    [∀ T, IsIso (f.val.app T)] : IsIso f := by
  let e := PresheafOfModules.isoMk (fun T ↦ asIso (f.val.app T))
    (fun {_ _} g ↦ f.val.naturality g)
  have : IsIso f.val := by
    change IsIso e.hom
    infer_instance
  have : IsIso ((SheafOfModules.forget R).map f) := ‹IsIso f.val›
  exact isIso_of_reflects_iso f (SheafOfModules.forget _)

-- Check restriction components with abstract sheaves, before unfolding a pullback object.
private theorem isIso_overMap_of_components
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {U V : C} (j : U ⟶ V)
    {M N : SheafOfModules.{u} (R.over V)} (f : M ⟶ N)
    (h : ∀ A : Over U, IsIso (f.val.app (op ((Over.map j).obj A)))) :
    IsIso ((overMap R j).map f) := by
  have hc (T : (Over U)ᵒᵖ) : IsIso (((overMap R j).map f).val.app T) := h T.unop
  exact isIso_of_components ((overMap R j).map f)

private theorem isIso_of_overMap_app
    {C : Type*} [Category* C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {U V : C} (j : U ⟶ V)
    {M N : SheafOfModules.{u} (R.over V)} (f : M ⟶ N)
    [IsIso ((overMap R j).map f)] (A : Over U) :
    IsIso (f.val.app (op ((Over.map j).obj A))) := by
  exact (SheafOfModules.evaluation.{u} (R.over U) (op A)).map_isIso
    ((overMap R j).map f)

-- Sectionwise pullbacks require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
private theorem binarySubmodule_on_W
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map
        (binarySubmoduleInclusion X W V H Q ι)) := by
  let R := moduleRings X.toRingedSpace
  let jV : V ⟶ W ⊔ V := homOfLE le_sup_right
  let jW : W ⟶ W ⊔ V := homOfLE le_sup_left
  let f := binarySubmoduleInclusion X W V H Q ι
  apply isIso_overMap_of_components jW f
  intro T
  let A : Over (W ⊔ V) := (Over.map jW).obj T
  let B : Over V := (Over.pullback jV).obj A
  have hB : B.left ≤ W ⊓ V :=
    le_inf ((leOfHom (pullback.fst A.hom jV)).trans T.hom.le)
      B.hom.le
  have hι : IsIso (ι.val.app (op B)) := by
    exact isIso_of_overMap_app (homOfLE (inf_le_right : W ⊓ V ≤ V)) ι
      (Over.mk (homOfLE hB))
  have hm : IsIso ((binarySubmoduleMap X W V H Q ι).val.app (op A)) := by
    dsimp [binarySubmoduleMap, SheafOfModules.overPullback, SheafOfModules.pushforward,
      PresheafOfModules.pushforward, PresheafOfModules.restrictScalars,
      PresheafOfModules.pushforward₀]
    have : IsIso ((ι ≫ (binarySubmoduleRestrictionIso X W V H).inv).val.app (op B)) := by
      change IsIso (ι.val.app (op B) ≫
        (binarySubmoduleRestrictionIso X W V H).inv.val.app (op B))
      have : IsIso ((binarySubmoduleRestrictionIso X W V H).inv.val.app (op B)) :=
        (SheafOfModules.evaluation.{u} _ (op B)).map_isIso
          (binarySubmoduleRestrictionIso X W V H).inv
      infer_instance
    exact (ModuleCat.restrictScalars _).map_isIso
      ((ι ≫ (binarySubmoduleRestrictionIso X W V H).inv).val.app (op B))
  have hp := (SheafOfModules.evaluation.{u} (R.over (W ⊔ V)) (op A)).map_isPullback
    (IsPullback.of_hasPullback
      ((binarySubmoduleAdjunction X W V).unit.app (H.over (W ⊔ V)))
      (binarySubmoduleMap X W V H Q ι))
  exact hp.isIso_fst_of_isIso hm

/-- The explicit pullback is the prescribed submodule on V and the ambient module on W.
Source: Stacks Project, Properties, Lemma 01PF (lemma-extend), binary gluing step.
(blueprint: lem-weil-pbc-module-submodule-binary-gluing-restrictions).

Proof: On an open T contained in V the unit from H(T) to H(T intersect V) is the
identity after the canonical restriction identifications. The pullback of this
identity along Q(T) -> H(T) is Q(T). The second pullback projection therefore gives
an isomorphism on V, natural in T. On an open T contained in W, T intersect V is
contained in W intersect V. The component of the given inclusion on this open is
an isomorphism, by the hypothesis and further restriction. Consequently the first
pullback projection is an isomorphism on T. Evaluation preserves pullbacks of module
sheaves, so these sectionwise identifications are isomorphisms of module sheaves.
They remain valid for empty opens and disjoint or repeated cover members. No local
presentation or finite-generation hypothesis is used. -/
theorem binarySubmodule_restrictions
    (X : Scheme.{u}) (W V : X.Opens)
    (H : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (Q : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (ι : Q ⟶ H.over V)
    [IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ⊓ V ≤ V from inf_le_right))).map ι)] :
    IsIso ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).map
        (binarySubmoduleInclusion X W V H Q ι)) ∧
      Nonempty ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj
          (binarySubmodule X W V H Q ι) ≅ Q)  := by
  exact ⟨binarySubmodule_on_W X W V H Q ι, binarySubmodule_on_V X W V H Q ι⟩

end AlgebraicGeometry.Scheme.Modules
