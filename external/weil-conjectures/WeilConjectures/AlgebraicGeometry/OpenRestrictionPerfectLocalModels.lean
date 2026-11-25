/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Recovering local perfect models from an open restriction

Source: Stacks Project, Definition 08CM and the locality argument in Tag 08DP.
(blueprint: lem-pc-open-restriction-perfect-local-models).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictIsoEquivalence {Y Z : Scheme.{u}} (s : Y ≅ Z) :
    SheafOfModules.{u} (moduleRings Y.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Z.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (Modules.restrictFunctor s.inv) (Modules.restrictFunctor s.hom)
    ((Modules.restrictFunctorComp s.hom s.inv).symm ≪≫
      Modules.restrictFunctorCongr s.hom_inv_id ≪≫ Modules.restrictFunctorId).symm
    ((Modules.restrictFunctorComp s.inv s.hom).symm ≪≫
      Modules.restrictFunctorCongr s.inv_hom_id ≪≫ Modules.restrictFunctorId)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A perfect restriction to U supplies ambient strictly perfect models at points of U.
Source: Stacks Project, Definition 08CM, used in the proof of Tag 08DP.
(blueprint: lem-pc-open-restriction-perfect-local-models).

Proof: At x in U, choose the strictly perfect model on an open W of U given by
perfectness of the restriction. The image of W under the open inclusion is an open
A of X containing x. The localized site of U at W is canonically equivalent to the
localized site of X at A, with the same restricted structure sheaf. Transport the
complex termwise across this exact equivalence. It preserves zero objects, finite
free modules and the retraction equations, so the transported complex is strictly
perfect with the same bounds. The composition comparison for exact restriction,
localized at quasi-isomorphisms, identifies its derived image with E restricted to A.
Compose this comparison with the given local-model isomorphism. No support or direct
image is involved. For U empty there are no points to test; U total gives the original
local models. -/
theorem open_restriction_perfect_local_models (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedCategory X)
    (hE : IsPerfect U.toScheme ((schemeOpenRestriction X U).mapDerivedCategory.obj E))
    (x : X) (hx : x ∈ U) :
    ∃ A : X.Opens, x ∈ A ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over A)) ℤ,
        IsStrictlyPerfect X A K ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) A).mapDerivedCategory.obj E ≅
            DerivedCategory.Q.obj K) := by
  classical
  obtain ⟨W, hxW, K, hK, ⟨iK⟩⟩ := hE (⟨x, hx⟩ : U.toScheme)
  let A := U.ι ''ᵁ W
  let s := U.ι.isoImage W
  let eW := Modules.overEquiv W
  let eA := Modules.overEquiv A
  let eS := restrictIsoEquivalence s
  let e := (eW.trans eS).trans eA.symm
  let H := e.functor
  have : H.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  have : H.Additive := Functor.additive_of_preserves_binary_products _
  let K' := (H.mapHomologicalComplex (.up ℤ)).obj K
  have hunit : H.obj (SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over W)) ≅
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over A) :=
    eA.inverse.mapIso (eS.functor.mapIso
      (W.sheafOfModulesEquivOverUnit (moduleRings U.toScheme.toRingedSpace)) ≪≫
      Modules.restrictUnitIso s.inv) ≪≫
    A.sheafOfModulesEquivOverInverseUnit (moduleRings X.toRingedSpace)
  have hfree (m : ℕ) : H.obj
      (SheafOfModules.free (R := (moduleRings U.toScheme.toRingedSpace).over W)
        (ULift.{u} (Fin m))) ≅
      SheafOfModules.free (R := (moduleRings X.toRingedSpace).over A)
        (ULift.{u} (Fin m)) :=
    (asIso (sigmaComparison H (fun _ : ULift.{u} (Fin m) ↦
      SheafOfModules.unit ((moduleRings U.toScheme.toRingedSpace).over W)))).symm ≪≫
        Sigma.mapIso (fun _ ↦ hunit)
  have hK' : IsStrictlyPerfect X A K' := by
    obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
    constructor
    · exact ⟨a, b, fun n hn ↦ H.map_isZero (hb n hn)⟩
    · intro n
      obtain ⟨m, ι, π, hιπ⟩ := hp n
      let t := hfree m
      refine ⟨m, H.map ι ≫ t.hom, t.inv ≫ H.map π, ?_⟩
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hιπ]
      exact H.map_id _
  let L := schemeOpenRestriction X U
  let rW := SheafOfModules.overFunctor.{u} (moduleRings U.toScheme.toRingedSpace) W
  let rA := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) A
  let square₀ : ((L ⋙ rW) ⋙ eW.functor) ⋙ eS.functor ≅ rA ⋙ eA.functor := by
    refine Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft L (Modules.overFunctorEquiv W) ≪≫
        Functor.isoWhiskerRight (Modules.overFunctorEquiv U) _ ≪≫
        (Modules.restrictFunctorComp W.ι U.ι).symm) _ ≪≫
      (Modules.restrictFunctorComp s.inv (W.ι ≫ U.ι)).symm ≪≫
      Modules.restrictFunctorCongr (U.ι.isoImage_inv_ι W) ≪≫
      (Modules.overFunctorEquiv A).symm
  let square : (L ⋙ rW) ⋙ H ≅ rA := by
    change (L ⋙ rW) ⋙ ((eW.functor ⋙ eS.functor) ⋙ eA.inverse) ≅ rA
    exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
      Functor.isoWhiskerRight square₀ eA.inverse ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft rA eA.unitIso.symm ≪≫ Functor.rightUnitor _
  have hxA : x ∈ A := by
    exact ⟨(⟨x, hx⟩ : U.toScheme), hxW, rfl⟩
  refine ⟨A, hxA, K', hK', ?_⟩
  let squareD : (L.mapDerivedCategory ⋙ rW.mapDerivedCategory) ⋙ H.mapDerivedCategory ≅
      rA.mapDerivedCategory :=
    (Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso L rW) _) ≪≫
      Functor.mapDerivedCategoryCompIso (L ⋙ rW) H ≪≫
      Functor.mapDerivedCategoryNatIso square
  exact ⟨(squareD.app E).symm ≪≫ H.mapDerivedCategory.mapIso iK ≪≫
    H.mapDerivedCategoryFactors.app K⟩


end AlgebraicGeometry.Scheme
