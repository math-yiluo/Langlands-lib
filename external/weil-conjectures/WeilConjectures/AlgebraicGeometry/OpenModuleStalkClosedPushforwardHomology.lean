/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Homology of a localized closed-pushforward stalk complex

Source: Stacks Project, Sheaves, Tag 00AE, and Modules, Tag 01AG.
(blueprint: lem-sc-open-module-stalk-closed-pushforward-homology).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A complex derived-isomorphic to a restricted closed pushforward has the expected
stalk homology. No boundedness or projectivity of its terms is assumed or asserted.
Source: Stacks Project, Sheaves, Tag 00AE, and Modules, Tag 01AG;
steps 3 and 4 of lem-sc-strict-perfect-closed-pushforward-stalk-model.
(blueprint: lem-sc-open-module-stalk-closed-pushforward-homology).

Proof: the equivalence of the slice site with the open-subspace site is exact.
Module stalks commute with kernels and cokernels by Tag 01AG, and restriction
of scalars along the open immersion's stalk ring map is exact. The composite
therefore preserves homology and quasi-isomorphisms and induces a functor on
derived categories. Apply it to e. Neighbourhoods inside U are cofinal at i(x),
so the stalk of the restriction of a sheaf agrees with its original stalk.
Apply nonempty_restriction_stalk_extension_iso to the single complex of that
sheaf and evaluate in degree zero. Restrict scalars, then cancel extension of
scalars using the adjunction unit, which is invertible since the ring map is
an isomorphism. Compose with overFunctorEquiv to obtain the required linear
coefficient isomorphism. Compatibility with the single functor
identifies the resulting object with the original pushforward stalk in degree
zero. Homology of a single complex is zero away from zero and is its coefficient
module at zero. Tag 00AE identifies the pushforward stalk with the source stalk;
the germ formula in closedImmersion_pushforward_stalks gives linearity through
(i.stalkMap x).hom. The stalk of the source unit sheaf identifies linearly with
the source stalk ring by its germ map. Compose these identifications. -/
theorem openModuleStalk_closedPushforward_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (x : Z) (U : Y.Opens) (hx : i x ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      DerivedCategory.Q.obj K) :
    let L := ((openModuleStalkFunctor Y U ⟨i x, hx⟩).mapHomologicalComplex (.up ℤ)).obj K
    Nonempty (L.homology 0 ≅
      ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) ∧
      (∀ j : ℤ, j ≠ 0 → IsZero (L.homology j)) := by
  let C := ModuleCat.{u} (Y.presheaf.stalk (U.ι ⟨i x, hx⟩))
  let : HasDerivedCategory.{u + 1}
      (ModuleCat.{u} (Y.presheaf.stalk (U.ι ⟨i x, hx⟩))) :=
    HasDerivedCategory.standard _
  let S := openModuleStalkFunctor Y U ⟨i x, hx⟩
  let R := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let M := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let L := (S.mapHomologicalComplex (.up ℤ)).obj K
  let N := S.obj (R.obj M)
  let d : DerivedCategory.Q.obj L ≅ (DerivedCategory.singleFunctor C 0).obj N :=
    (S.mapDerivedCategoryFactors.app K).symm ≪≫
      (S.mapDerivedCategory.mapIso e).symm ≪≫
      S.mapDerivedCategory.mapIso ((R.mapDerivedCategorySingleFunctor 0).app M) ≪≫
      (S.mapDerivedCategorySingleFunctor 0).app (R.obj M)
  let y : U.toScheme := ⟨i x, hx⟩
  let ρ := (U.ι.stalkMap y).hom
  let A := ModuleCat.restrictScalars ρ
  let B := ModuleCat.extendScalars ρ
  let P := (RingedSpace.moduleStalkFunctor Y.toRingedSpace (i x)).obj M
  let V := (HomologicalComplex.single Y.Modules (.up ℤ) 0).obj M
  obtain ⟨c⟩ := nonempty_restriction_stalk_extension_iso U.ι y V
  let c₀ := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso c
  let c₁ : B.obj P ≅
      (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M) := by
    change B.obj ((RingedSpace.moduleStalkFunctor Y.toRingedSpace (i x)).obj
      (V.X 0)) ≅ (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj (V.X 0)) at c₀
    simpa only [V, HomologicalComplex.single_obj_X_self] using c₀
  let eρ := RingEquiv.ofBijective ρ
    (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap y))
  have : A.IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  let a : N ≅ P :=
    A.mapIso ((RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).mapIso
      ((Scheme.Modules.overFunctorEquiv U).app M)) ≪≫
      (A.mapIso c₁).symm ≪≫ (asIso ((ModuleCat.extendRestrictScalarsAdj ρ).unit.app P)).symm
  obtain ⟨eu, _, _⟩ := Scheme.ideal_module_product_stalk
    (𝟙 (SheafOfModules.unit Z.ringCatSheaf))
    (SheafOfModules.unit Z.ringCatSheaf) x
  let G := SheafOfModules.unit Z.ringCatSheaf
  let T := ModuleCat.restrictScalars (i.stalkMap x).hom
  obtain ⟨hb, _, hl⟩ := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 x
  let f : (RingedSpace.moduleStalkFunctor Y.toRingedSpace (i x)).obj M →ₗ[
      Y.presheaf.stalk (i x)]
      T.obj ((RingedSpace.moduleStalkFunctor Z.toRingedSpace x).obj G) :=
    { (ConcreteCategory.hom
        (TopCat.Presheaf.stalkPushforward Ab i.base G.val.presheaf x)) with
      map_smul' := by
        intro r m
        exact hl r m }
  let b := (LinearEquiv.ofBijective f hb).toModuleIso ≪≫ T.mapIso eu
  refine ⟨⟨?zero⟩, ?other⟩
  case zero =>
    exact (DerivedCategory.homologyFunctorFactors C 0).symm.app L ≪≫
      (DerivedCategory.homologyFunctor C 0).mapIso d ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app N ≪≫ a ≪≫ b
  case other =>
    intro j hj
    let q := (HomologicalComplex.single C (.up ℤ) 0).obj N
    let h : L.homology j ≅ q.homology j :=
      (DerivedCategory.homologyFunctorFactors C j).symm.app L ≪≫
        (DerivedCategory.homologyFunctor C j).mapIso d ≪≫
        (DerivedCategory.homologyFunctorFactors C j).app q
    exact h.isZero_iff.mpr (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 N j hj)

end AlgebraicGeometry
