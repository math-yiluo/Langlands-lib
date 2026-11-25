/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.CategoryTheory.Presentable.Directed
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-! # Canonical directed affine stages at a separable generic point

This module records the reindexed system coming from the affine pointed
neighbourhoods of the geometric generic point.  The index, diagram, and maps are
required to be the canonical ones, rather than arbitrary affine étale systems.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

noncomputable section

/-- The canonical affine pointed-neighbourhood system, reindexed by a directed
poset.  The displayed equations identify every field with the corresponding
canonical map in the strict-henselization diagram.

Source: Stacks Project, Tags 04HX and 0032; the library declarations
`strictHenselizationAffineProperties` and `exists_directed_reindexing`.
(blueprint: new-lem-pd-separable-generic-affine-etale-stages)

The proof first applies the directed-reindexing theorem to the opposite of the
small affine pointed-neighbourhood category.  It then transports the affine
stage maps, the transition maps, and the canonical cone legs along that
reindexing.  The affine and étale assertions are inherited from the affine
pointed-neighbourhood objects, and the displayed equations are the defining
equations of the strict-henselization cone and its structural maps.
-/
theorem exists_separableGeneric_affineEtale_stages
    (S : Scheme.{u}) [IsIntegral S]
    (Ω : Type u) [Field Ω] [Algebra S.functionField Ω]
    [IsAlgClosure S.functionField Ω] :
    let F := S.functionField
    letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    let η : Spec (CommRingCat.of Ω) ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ S.fromSpecFunctionField
    let J := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods η)
    letI : SmallCategory J := inferInstance
    let N := (equivSmallModel
      (Scheme.strictHenselizationNeighbourhoods η)).inverse
    let D₀ := (Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec
    ∃ (A : Type u) (_ : Preorder A) (_ : IsDirected A (· ≤ ·)) (_ : Nonempty A)
      (R : A ⥤ Jᵒᵖ) (_ : Functor.Initial R.op)
      (π₀ : ∀ i : Aᵒᵖ,
        Spec (Scheme.strictHenselizationRing η) ⟶ (R.op ⋙ D₀).obj i)
      (u : ∀ i : A, (R.op ⋙ D₀).obj (op i) ⟶ S),
      (∀ {i j : Aᵒᵖ} (f : i ⟶ j),
        π₀ j = π₀ i ≫ (R.op ⋙ D₀).map f) ∧
      (∀ i : A, IsAffine ((R.op ⋙ D₀).obj (op i))) ∧
      (∀ i : A, Etale (u i)) ∧
      (∀ {i j : A} (h : i ≤ j),
        u j = (R.op ⋙ D₀).map (homOfLE h).op ≫ u i) ∧
      (∀ {i j : A} (h : i ≤ j),
        IsAffineHom ((R.op ⋙ D₀).map (homOfLE h).op)) ∧
      (∀ j : Aᵒᵖ,
        π₀ j = (Scheme.strictHenselizationCone η).π.app (R.op.obj j)) ∧
      (∀ i : A,
        u i =
          Spec.map (Scheme.ΓSpecIso
            (Opposite.unop ((N.obj (Opposite.unop (R.obj i))).1.left))).inv ≫
            ((Scheme.AffineEtale.Spec S).obj
              (N.obj (Opposite.unop (R.obj i))).1).hom) := by
  intro F η J N D₀
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed S.functionField
  have : IsCofiltered J := (Scheme.strictHenselization_properties η).2.1
  obtain ⟨A, _, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Jᵒᵖ
  have haff (i : Aᵒᵖ) : IsAffine ((R.op ⋙ D₀).obj i) := inferInstanceAs (IsAffine (Spec _))
  refine ⟨A, inferInstance, hdir, hne, R, inferInstance,
    fun i ↦ (Scheme.strictHenselizationCone η).π.app (R.op.obj i),
    fun i ↦ Spec.map (Scheme.ΓSpecIso _).inv ≫
      ((Scheme.AffineEtale.Spec S).obj (N.obj (unop (R.obj i))).1).hom,
    fun f ↦ ((Scheme.strictHenselizationCone η).w (R.op.map f)).symm,
    fun _ ↦ haff _, fun i ↦ ?_, fun h ↦ ?_, fun _ ↦ inferInstance,
    fun _ ↦ rfl, fun _ ↦ rfl⟩
  · have := ((Scheme.AffineEtale.Spec S).obj (N.obj (unop (R.obj i))).1).prop
    infer_instance
  · have hw := MorphismProperty.Over.w
      ((Scheme.AffineEtale.Spec S).map (N.map (R.map (homOfLE h)).unop).1)
    dsimp [D₀, Scheme.strictHenselizationAffineDiagram,
      Scheme.strictHenselizationCoordinateRings]
    rw [← Scheme.isoSpec_Spec_inv, ← Scheme.isoSpec_Spec_inv]
    exact (congrArg (_ ≫ ·) hw.symm).trans (@Scheme.isoSpec_inv_naturality_assoc _ _
      (inferInstanceAs (IsAffine (Spec _))) (inferInstanceAs (IsAffine (Spec _))) _ _ _).symm

end
end AlgebraicGeometry
