/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism

/-! # Local pullback adjunction on stalks

Source: Stacks Project, Tags 01J7 and 0098.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry

/-- The adjoint of an invertible local tensor-pullback comparison is invertible
on the original stalk. Source: Stacks, Tags 01J7 and 0098.
(blueprint: lem-weil-pbc-local-pullback-adjoint-stalk-iso)

Proof: At the closed point, the pullback-unit stalk followed by the direct-image
stalk comparison is the canonical module-stalk isomorphism. The direct-image
comparison is invertible because the local-spectrum map is inducing. Cancel this
comparison to get invertibility of the unit on the original stalk. The adjoint
of beta is the unit followed by the direct image of beta; both induce invertible
stalk maps. Transport the source point by the closed-point image equality. -/
theorem localPullback_adjoint_stalk_isIso (Y : Scheme.{u}) (y : Y)
    (G : Y.Modules) (H : (Spec (Y.presheaf.stalk y)).Modules)
    (beta : (Scheme.Modules.tensorPullback (Y.fromSpecStalk y)).obj G ⟶ H)
    [IsIso beta] :
    IsIso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (Y.fromSpecStalk y))).homEquiv _ _ beta)) := by
  let c := Y.fromSpecStalk y
  let z : Spec (Y.presheaf.stalk y) := IsLocalRing.closedPoint (Y.presheaf.stalk y)
  let A := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction c)
  let T := (Scheme.Modules.tensorPullback c).obj G
  let S := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (c z)
  let q := T.presheaf.stalkPushforward AddCommGrpCat.{u} c.base z
  have hq : IsIso q :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} c.isEmbedding.isInducing T.presheaf z
  obtain ⟨e, he⟩ := Scheme.fromSpecStalk_module_stalk Y y G
  have hcomp : S.map ((PresheafOfModules.toPresheaf _).map
      (A.unit.app G).val) ≫ q = (forget₂ _ AddCommGrpCat.{u}).map e.hom := by
    ext m
    obtain ⟨V, hy, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf m
    change q (S.map ((PresheafOfModules.toPresheaf _).map
      (A.unit.app G).val) (TopCat.Presheaf.germ G.presheaf V (c z) hy s)) = _
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    erw [TopCat.Presheaf.stalkPushforward_germ_apply]
    exact (he V hy s).symm
  have hu : IsIso (S.map ((PresheafOfModules.toPresheaf _).map
      (A.unit.app G).val)) := by
    have : IsIso (S.map ((PresheafOfModules.toPresheaf _).map
        (A.unit.app G).val) ≫ q) := by rw [hcomp]; infer_instance
    exact IsIso.of_isIso_comp_right _ q
  have hm : IsIso ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (c z)).map
      (A.homEquiv _ _ beta)) := by
    rw [← isIso_iff_of_reflects_iso _ (forget₂ _ AddCommGrpCat.{u})]
    rw [Adjunction.homEquiv_unit]
    change IsIso (S.map ((PresheafOfModules.toPresheaf _).map
      ((A.unit.app G) ≫ (Scheme.Modules.pushforward c).map beta).val))
    rw [SheafOfModules.comp_val, Functor.map_comp, Functor.map_comp]
    have hb : IsIso ((PresheafOfModules.toPresheaf _).map
        ((Scheme.Modules.pushforward c).map beta).val) := by
      change IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((Scheme.Modules.pushforward c).map beta))
      infer_instance
    exact IsIso.comp_isIso
  dsimp only [A, c, z] at hm
  rw [Scheme.fromSpecStalk_closedPoint] at hm
  exact hm

end AlgebraicGeometry
