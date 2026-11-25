/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import Mathlib.CategoryTheory.Whiskering

/-! # Finite pushforward comparison for curve assertions

Source: Stacks Project, Lemma 0A5D (lemma-finite-pushforward-statements).
(blueprint: g1-finite-pushforward-cohomology-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private noncomputable def coefficientRoundTrip (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      AddCommGrpCat.{u + 1})).obj ((sheafCompose _ E).obj F) ≅ F := by
  dsimp only
  apply ObjectProperty.isoMk
  exact Functor.isoWhiskerLeft F.obj (forget₂ (ModuleCat.{u + 1} ℤ)
    AddCommGrpCat.{u + 1}).asEquivalence.counitIso

/-- Source: Stacks Project, Lemma 0A5D, cohomology step
(blueprint: g1-finite-pushforward-cohomology-comparison).
Proof: the finite edge map is bijective because finite direct image is exact and preserves
injectives. It identifies cohomology on the source with cohomology of its direct image.
The coefficient equivalence followed by forgetting has the original abelian sheaf as its
underlying sheaf, so the same comparison applies to the sheaves in the curve assertions. -/
theorem IsCurve.finite_pushforward_cohomology_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (_hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    ∀ q : ℕ, Nonempty
      (Sheaf.H ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj FY) q ≃+
        Sheaf.H ((sheafCompose _
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})).obj FX) q) := by
  classical
  dsimp only
  intro q
  let h := (Sheaf.H.map
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app P.F) q).comp
    (Etale.cohomologyMap f _ q)
  have hb : Function.Bijective h := Etale.bijective_edgeMap_of_isFinite f P.F q
  let e := AddEquiv.ofBijective h hb
  let ey := coefficientRoundTrip Y ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F)
  let ex := coefficientRoundTrip P.C P.F
  let eyH : Sheaf.H _ q ≃+ Sheaf.H _ q :=
    { toFun := Sheaf.H.map ey.hom q
      invFun := Sheaf.H.map ey.inv q
      left_inv := by
        intro x
        rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := by
        intro x
        rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
      map_add' := map_add _ }
  let exH : Sheaf.H _ q ≃+ Sheaf.H _ q :=
    { toFun := Sheaf.H.map ex.hom q
      invFun := Sheaf.H.map ex.inv q
      left_inv := by
        intro x
        rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := by
        intro x
        rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]
      map_add' := map_add _ }
  exact ⟨eyH.trans (e.trans exH.symm)⟩

end AlgebraicGeometry
