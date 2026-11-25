/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Mathlib.Topology.Sheaves.Stalks

/-! # Vanishing of derived restriction away from cohomological support
Source: Stacks Project, Tags 0A9A and 05RU.
(blueprint: lem-pc-supported-derived-restriction-zero).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry

private theorem module_restriction_zero
    (X : Scheme.{u}) (T : Set X) (U : X.Opens) (hU : (U : Set X) ⊆ Tᶜ)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hM : ∀ x : X, x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk M.val.presheaf x))) :
    IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext V z
  change z = 0
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj M)
  intro x hx
  change TopCat.Presheaf.germ M.val.presheaf _ x hx _ = TopCat.Presheaf.germ M.val.presheaf _ x hx _
  exact (hM x (hU (leOfHom V.unop.hom hx))).elim _ _

/-- A derived object with cohomology supported on T restricts to zero outside T.
Source: Stacks Project, Tag 0A9A, affine proof, and Tag 05RU.
(blueprint: lem-pc-supported-derived-restriction-zero).

Proof:
1. Restriction of module sheaves to an open is exact and commutes with cohomology.
2. At a point of U, each cohomology stalk is the corresponding stalk on X and is zero
   by the support assumption. A module sheaf with all stalks zero is zero.
3. Thus all homology objects of the derived restriction vanish; homology detects zero
   in the derived category of module sheaves. This also covers the empty open. -/
theorem supported_derived_restriction_zero
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (T : Set X) (U : X.Opens) (hU : (U : Set X) ⊆ Tᶜ)
    (K : schemeDerivedCategory X)
    (hK : ∀ (n : ℤ) (x : X), x ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) :
    IsZero (((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory).obj K) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let L := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hz (n : ℤ) : IsZero (F.obj (L.homology n)) := by
    have h := module_restriction_zero X T U hU
      ((DerivedCategory.homologyFunctor C n).obj K) (hK n)
    exact h.of_iso (F.mapIso
      (((DerivedCategory.homologyFunctorFactors C n).app L).symm ≪≫
        (DerivedCategory.homologyFunctor C n).mapIso e))
  let L' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hz' (n : ℤ) : IsZero (L'.homology n) := by
    exact (hz n).of_iso ((L.sc n).mapHomologyIso F)
  have hQ : IsZero (DerivedCategory.Q.obj L') := by
    have hhom (n : ℤ) : IsZero
        ((DerivedCategory.homologyFunctor D n).obj (DerivedCategory.Q.obj L')) :=
      (hz' n).of_iso ((DerivedCategory.homologyFunctorFactors D n).app L')
    have hi : IsIso (0 : DerivedCategory.Q.obj L' ⟶ 0) :=
      (DerivedCategory.isIso_iff D _).mpr (fun n ↦ by
        exact IsZero.isIso (hhom n) ((DerivedCategory.homologyFunctor D n).map_isZero
          (isZero_zero _)) _)
    exact (isZero_zero _).of_iso (asIso (0 : DerivedCategory.Q.obj L' ⟶ 0))
  exact hQ.of_iso
    ((F.mapDerivedCategory.mapIso e).symm ≪≫ F.mapDerivedCategoryFactors.app L)

end AlgebraicGeometry
