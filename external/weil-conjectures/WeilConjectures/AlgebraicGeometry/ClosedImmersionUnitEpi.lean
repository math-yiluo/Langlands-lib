/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Epimorphism of the closed immersion pullback unit

Source: Stacks Project, Modules, Lemma 08KS.
(blueprint: lem-weil-pbc-closed-immersion-unit-epi).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry TopologicalSpace Opposite
open scoped ChangeOfRings
open ZeroObject
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- The unit of tensor pullback along a closed immersion is epi, by the stalkwise
quotient computation of Stacks Project, Modules, Lemma 08KS.
(blueprint: lem-weil-pbc-closed-immersion-unit-epi)
-/
theorem closedImmersion_unit_epi {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (F : Y.Modules) :
    Epi ((Classical.choice (nonempty_tensorPullbackAdjunction i)).unit.app F) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction i)
  have hs (x : Y) : Function.Surjective
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map (adj.unit.app F)) := by
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨e, he⟩ := exists_tensorPullback_stalk_iso i z
      let c := TopCat.Presheaf.stalkPushforward Ab i.base
        ((tensorPullback i).obj F).presheaf z
      have hc := (closedImmersion_pushforward_stalks i i.isClosedEmbedding
        ((tensorPullback i).obj F)).2.1 z
      let R := Y.presheaf.stalk (i.base z)
      let S := Z.presheaf.stalk z
      let : Algebra R S := (i.stalkMap z).hom.toAlgebra
      have ht := TensorProduct.mk_surjective (R := R) (S := S)
        (M := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (i.base z)).obj F)
        (i.stalkMap_surjective z)
      intro t
      obtain ⟨m, hm⟩ := ht ((e.hom.app F) (c t))
      obtain ⟨V, hz, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf m
      refine ⟨TopCat.Presheaf.germ F.presheaf V (i.base z) hz s, ?_⟩
      apply hc.1.1
      apply (ModuleCat.mono_iff_injective (e.hom.app F)).mp inferInstance
      change (e.hom.app F) (c
        ((TopCat.Presheaf.stalkFunctor Ab (i.base z)).map
          (adj.unit.app F).mapPresheaf
          (TopCat.Presheaf.germ F.presheaf V (i.base z) hz s))) = _
      dsimp only [c]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
        TopCat.Presheaf.stalkPushforward_germ_apply]
      exact (he F V hz s).trans hm
    · have hzero : Subsingleton (↥(TopCat.Presheaf.stalk
          ((pushforward i).obj ((tensorPullback i).obj F)).presheaf x)) :=
        (closedImmersion_pushforward_stalks i i.isClosedEmbedding
        ((tensorPullback i).obj F)).1 x hx
      intro t
      exact ⟨0, hzero.elim _ _⟩
  have hep : Epi (adj.unit.app F) := by
    constructor
    intro W a b hab
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext m
    apply TopCat.Presheaf.section_ext ⟨W.presheaf, W.isSheaf⟩ (unop V)
    intro x hx
    obtain ⟨s, hs⟩ := hs x
      (TopCat.Presheaf.germ ((pushforward i).obj ((tensorPullback i).obj F)).presheaf
        (unop V) x hx m)
    have heq := congrArg (fun f : F ⟶ W ↦
      (TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf s) hab
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((adj.unit.app F).mapPresheaf ≫ a.mapPresheaf) s =
      (TopCat.Presheaf.stalkFunctor Ab x).map
        ((adj.unit.app F).mapPresheaf ≫ b.mapPresheaf) s at heq
    rw [Functor.map_comp, Functor.map_comp] at heq
    change (TopCat.Presheaf.stalkFunctor Ab x).map a.mapPresheaf
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map (adj.unit.app F) s) =
      (TopCat.Presheaf.stalkFunctor Ab x).map b.mapPresheaf
        ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).map (adj.unit.app F) s) at heq
    rw [hs] at heq
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at heq
    exact heq
  let adj' := Classical.choice (nonempty_tensorPullbackAdjunction i)
  rw [← adj.unit_leftAdjointUniq_hom_app adj' F]
  exact epi_comp _ _
end
end AlgebraicGeometry.Scheme.Modules
