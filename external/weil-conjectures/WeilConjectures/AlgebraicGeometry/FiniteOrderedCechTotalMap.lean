/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import all WeilConjectures.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso

/-! # Sectionwise quasi-isomorphisms of ordered Čech totals

Source: Stacks Project, Tags 01ET and 01EQ, finite-column comparison.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private instance presheaf_additive (X : Scheme.{u}) :
    (alternatingCechModulePresheaf (X := X)).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

-- Explicit product comparisons require additional elaboration of the composite functors.
set_option backward.isDefEq.respectTransparency false in
private theorem alternatingCechColumn_quasiIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens)
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i : F ⟶ J)
    (hi : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((alternatingCechModulePresheaf (X := X) ⋙
        (CategoryTheory.evaluation X.Opensᵒᵖ
          (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
            (op (alternatingCechIntersection U t))).mapHomologicalComplex (.up ℤ)).map i))
    (k : ℕ) :
    QuasiIso (((alternatingCechDoubleFunctor U).map i).f (k : ℤ)) := by
  classical
  let C := ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  let S := fun t : Fin (k + 1) ↪o Fin r ↦
    (alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ C).obj
        (op (alternatingCechIntersection U t))).mapHomologicalComplex (ComplexShape.up ℤ)
  let P := fun t ↦ (S t).obj F
  let Q := fun t ↦ (S t).obj J
  let a := fun t ↦ (S t).map i
  have (t : Fin (k + 1) ↪o Fin r) : QuasiIso (a t) :=
    hi k t
  have hprod : QuasiIso (Limits.Pi.map a) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n
    have (t : Fin (k + 1) ↪o Fin r) : IsIso (H.map (a t)) := by
      exact (quasiIsoAt_iff_isIso_homologyMap (a t) n).mp inferInstance
    have he : H.map (Limits.Pi.map a) ≫ piComparison H Q =
        piComparison H P ≫ Limits.Pi.map (fun t ↦ H.map (a t)) := by
      apply Limits.Pi.hom_ext
      intro t
      simp only [Category.assoc, piComparison_comp_π]
      erw [Limits.Pi.map_π]
      rw [← H.map_comp, Limits.Pi.map_π, H.map_comp]
      erw [piComparison_comp_π_assoc]
    change IsIso (H.map (Limits.Pi.map a))
    have : IsIso (H.map (Limits.Pi.map a) ≫ piComparison H Q) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (piComparison H Q)
  have := alternatingCechColumnProjection_isIso U F k
  have := alternatingCechColumnProjection_isIso U J k
  have hcomm : ((alternatingCechDoubleFunctor U).map i).f (k : ℤ) ≫
      Limits.Pi.lift (alternatingCechColumnProjection U J k) =
        Limits.Pi.lift (alternatingCechColumnProjection U F k) ≫ Limits.Pi.map a := by
    apply Limits.Pi.hom_ext
    intro t
    simp only [Category.assoc, Limits.Pi.lift_comp_π]
    erw [Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc]
    apply HomologicalComplex.hom_ext
    intro n
    change (HomologicalComplex.extendMap
      (alternatingCechComplexMap U ((alternatingCechModulePresheaf (X := X)).map
        (i.f n))) ComplexShape.embeddingUpNat).f (k : ℤ) ≫ _ = _
    erw [HomologicalComplex.extendMap_f _ _ (i := k) rfl]
    dsimp only [alternatingCechColumnProjection, HomologicalComplex.comp_f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have : QuasiIso (((alternatingCechDoubleFunctor U).map i).f (k : ℤ) ≫
      Limits.Pi.lift (alternatingCechColumnProjection U J k)) := by
    rw [hcomm]
    infer_instance
  exact (quasiIso_iff_comp_right _
    (Limits.Pi.lift (alternatingCechColumnProjection U J k))).mp inferInstance

/-- A sectionwise quasi-isomorphism on every ordered intersection induces a
quasi-isomorphism of the total complexes.
Source: Stacks Project, Tag 01ET and Homology, Tag 0133.
(auxiliary; not a blueprint node)
Proof: Each column is the finite product of section complexes, with the
canonical product isomorphism given by evaluation on increasing tuples.
Homology commutes with these products. Outside columns 0,...,r-1 all terms
vanish. The finite-column total comparison proves the assertion. -/
theorem orderedCechTotalMap_quasiIso
    (X : Scheme.{u}) (r : ℕ) (U : Fin r → X.Opens)
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (i : F ⟶ J)
    (hi : ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj
          (op (alternatingCechIntersection U t))).mapHomologicalComplex (.up ℤ)).map i)) :
    QuasiIso ((alternatingCechTotalFunctor U).map i) := by
  have := alternatingCechDouble_strictlyGE U F
  have := alternatingCechDouble_strictlyLE U F
  have := alternatingCechDouble_strictlyGE U J
  have := alternatingCechDouble_strictlyLE U J
  change QuasiIso (HomologicalComplex₂.total.map
    ((alternatingCechDoubleFunctor U).map i) (ComplexShape.up ℤ))
  apply HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns
    _ 0 ((r : ℤ) - 1)
  intro p hp _
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  apply alternatingCechColumn_quasiIso U F J i _ k
  intro p t
  let W := alternatingCechIntersection U t
  let E := SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
    PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op W)
  let R := ModuleCat.restrictScalars
    ((moduleRings X.toRingedSpace).obj.map (isTerminalTop.op.to (op W))).hom
  have : QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map i) := hi p t
  have : QuasiIso ((R.mapHomologicalComplex (.up ℤ)).map
    ((E.mapHomologicalComplex (.up ℤ)).map i)) := inferInstance
  exact this

end AlgebraicGeometry
