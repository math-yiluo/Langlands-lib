/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Common affine models for two perfect objects

Source: Stacks Project, Tag 08CR, affine localization in the second proof
(blueprint: lem-pc-perfect-common-affine-models).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem restrict_strictlyPerfect (X : Scheme.{u}) (U V : X.Opens) (h : V ≤ U)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K) :
    IsStrictlyPerfect X V
      (((SheafOfModules.overMap
        (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K) := by
  let F := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h)
  obtain ⟨⟨a, b, hb⟩, hp⟩ := hK
  constructor
  · exact ⟨a, b, fun n hn ↦ F.map_isZero (hb n hn)⟩
  · intro n
    obtain ⟨m, i, r, hir⟩ := hp n
    let e : F.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison F (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
        Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso (homOfLE h))
    refine ⟨m, F.map i ≫ e.hom, e.inv ≫ F.map r, ?_⟩
    change (F.map i ≫ e.hom) ≫ e.inv ≫ F.map r = 𝟙 (F.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hir]
    exact F.map_id _

private theorem restrict_model (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (U V : X.Opens) (h : V ≤ U) (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K) :
    Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj
        (((SheafOfModules.overMap
          (moduleRings X.toRingedSpace) (homOfLE h)).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let F := SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h)
  let G := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have : PreservesFiniteLimits (G ⋙ F) := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (G ⋙ F) := comp_preservesFiniteColimits _ _
  exact ⟨(Functor.mapDerivedCategoryNatIso
    (SheafOfModules.overFunctorMap (moduleRings X.toRingedSpace) (homOfLE h))).symm.app E ≪≫
      (Functor.mapDerivedCategoryCompIso G F).symm.app E ≪≫ F.mapDerivedCategory.mapIso e ≪≫
        F.mapDerivedCategoryFactors.app K⟩

/-- Two perfect objects have strictly perfect representatives on one affine neighbourhood
of any specified point. Source: Stacks Project, Tag 08CR, second proof, local reduction
(blueprint: lem-pc-perfect-common-affine-models).

Proof: At the specified point choose the neighbourhoods and strictly perfect complexes
in the definition of perfectness for E and F. Their intersection is an open neighbourhood.
Choose an affine open neighbourhood inside this intersection, using the affine basis of
scheme opens. Restrict both complexes to this smaller open. Restriction preserves zero
objects, finite free modules and the equation splitting each term off a finite free module;
thus it preserves strict perfectness, with the same degree bounds. The natural composition
isomorphism for open restriction, and the comparison between termwise restriction followed
by Q and derived restriction, transport the original representing isomorphisms to the new
open. This gives both models on the same affine neighbourhood. No separatedness hypothesis
is used: the intersection is refined to an affine open, not assumed affine itself. -/
theorem perfect_common_affine_models (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E F : schemeDerivedCategory X) (hE : IsPerfect X E) (hF : IsPerfect X F) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect X U A ∧ IsStrictlyPerfect X U B ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj A) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj F ≅
          DerivedCategory.Q.obj B) := by
  obtain ⟨U, hxU, A, hA, ⟨eA⟩⟩ := hE x
  obtain ⟨V, hxV, B, hB, ⟨eB⟩⟩ := hF x
  obtain ⟨W, hW, hxW, hsub⟩ :=
    exists_isAffineOpen_mem_and_subset (U := U ⊓ V) ⟨hxU, hxV⟩
  have hWU : W ≤ U := le_trans hsub inf_le_left
  have hWV : W ≤ V := le_trans hsub inf_le_right
  refine ⟨W, hxW, hW,
    ((SheafOfModules.overMap
      (moduleRings X.toRingedSpace) (homOfLE hWU)).mapHomologicalComplex (.up ℤ)).obj A,
    ((SheafOfModules.overMap
      (moduleRings X.toRingedSpace) (homOfLE hWV)).mapHomologicalComplex (.up ℤ)).obj B,
    restrict_strictlyPerfect X U W hWU A hA,
    restrict_strictlyPerfect X V W hWV B hB,
    restrict_model X U W hWU E A eA, restrict_model X V W hWV F B eB⟩

end AlgebraicGeometry.Scheme
