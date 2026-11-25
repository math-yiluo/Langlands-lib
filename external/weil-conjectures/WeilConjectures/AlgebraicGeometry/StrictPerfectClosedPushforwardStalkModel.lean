/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFreeProjective
import WeilConjectures.AlgebraicGeometry.OpenModuleStalkClosedPushforwardHomology

/-! # Bounded projective models of closed-pushforward stalks

Source: Stacks Project, Tags 00AE, 01AG, 08C4 and 08CM.
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-model).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Taking stalks of a local strictly perfect model gives a bounded complex of projectives
with the homology of the restricted source stalk in degree zero.

Source: Stacks Project, Sheaves Tag 00AE, Modules Tag 01AG, and Cohomology of Sheaves
Tags 08C4 and 08CM; steps 1 and 2 of the stalk-resolution argument.
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-model).

Proof. Regard the site over U as the open-subspace site and take the stalk at i(x).
The cofinality of neighbourhoods contained in U identifies the stalk rings and the
stalks of restricted sheaves with those on Y. Apply this stalk functor termwise to K.
It preserves zero objects, so the bounds a and b for K are also bounds for its stalk
complex L. It preserves finite coproducts: the germs of the standard generators
identify the stalk of the rank-m free sheaf with the free stalk module of rank m.
Applying the stalk functor to each finite-free retraction for K gives a retraction
of this free module onto L in that degree. A retract of a projective is projective.
By exactness of module stalks (Tag 01AG), this functor preserves homology and
quasi-isomorphisms and descends to the derived localization. Apply it to e. The
localized degree-zero sheaf has stalk in degree zero and no other homology.
Tag 00AE identifies the pushforward stalk at i(x) with the source stalk; its germ
map is linear through i.stalkMap x. For the unit sheaf the source stalk is its
stalk ring with the regular module structure. These identifications give the
stated degree-zero isomorphism; all other homology objects are zero. No
truncation, tail splitting or augmented resolution is asserted here. -/
theorem strictPerfectClosedPushforward_stalkModel
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (x : Z) (U : Y.Opens) (hx : i x ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hK : Y.IsStrictlyPerfect U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      DerivedCategory.Q.obj K) :
    ∃ L : CochainComplex (ModuleCat.{u} (Y.presheaf.stalk (i x))) ℤ,
      (∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (L.X j)) ∧
      (∀ j : ℤ, Projective (L.X j)) ∧
      Nonempty (L.homology 0 ≅
        ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
          (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) ∧
      (∀ j : ℤ, j ≠ 0 → IsZero (L.homology j)) := by
  let S := openModuleStalkFunctor Y U ⟨i x, hx⟩
  let L := (S.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨hzero, hother⟩ := openModuleStalk_closedPushforward_homology i x U hx K e
  refine ⟨L, ?_, ?_, hzero, hother⟩
  · obtain ⟨a, b, hab⟩ := hK.1
    exact ⟨a, b, fun j hj ↦ S.map_isZero (hab j hj)⟩
  · intro j
    obtain ⟨m, ι, π, hιπ⟩ := hK.2 j
    have : Projective (S.obj (SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))) :=
      openModuleStalk_free_projective Y U ⟨i x, hx⟩ m
    exact (show Retract (L.X j) (S.obj (SheafOfModules.free
      (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin m)))) from
        ⟨S.map ι, S.map π, by
          change S.map ι ≫ S.map π = 𝟙 (S.obj (K.X j))
          rw [← S.map_comp, hιπ, S.map_id]⟩).projective

end AlgebraicGeometry
