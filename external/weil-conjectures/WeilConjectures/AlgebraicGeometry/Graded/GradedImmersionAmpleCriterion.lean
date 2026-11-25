/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedLineMap
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection
import all WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import all WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.RelativeGradedLineMap.RelativeGradedMapAffineChart
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Proj.ProjQcOpenTwistAmple
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-!
# Graded immersion criterion for ampleness

Source: Stacks Project, Morphisms, Tag 01VJ, implication (6) implies (1), with
Constructions, Tag 01O9 (blueprint: lem-trf-graded-immersion-ample-criterion).
-/

@[expose] public section

set_option linter.privateModule false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem boundary_adj_eq {X Y : Scheme.{u}} (j : X ⟶ Y) :
    Classical.choose (exists_tensorPullbackAdjunction j) =
      tensorPullbackSectionAdjunction j := by
  apply (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction j)).2
  intro M U s
  exact (Classical.choose_spec (exists_tensorPullbackAdjunction j)) M (op U) s

private theorem boundary_unit_transport {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((boundaryPullbackComparison j).app M).hom.app (j ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction j).unit.app M).app U s) =
        pullbackSection j s := by
  unfold boundaryPullbackComparison
  rw [boundary_adj_eq]
  exact congrArg (fun f ↦ f.app U s)
    ((tensorPullbackSectionAdjunction j).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction j) M)

private theorem evaluate_one
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1)) :
    ψ.evaluate j V q 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      unitSectionsEquiv ⊤ 1 := by
  unfold RelativeGradedLineMap.evaluate
  rw [ψ.one]
  change (pullbackObjUnitIso j).hom.app ⊤
    (((boundaryPullbackComparison j).app _).hom.app ⊤
      (((tensorPullback j).obj _).presheaf.map (homOfLE q).op
        (((tensorPullbackSectionAdjunction j).unit.app _).app _
          (unitSectionsEquiv _ 1)))) = _
  have hc := Hom.app_presheaf_map
    ((boundaryPullbackComparison j).app (unit Z)).hom (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app (unit Z)).app (h ⁻¹ᵁ V.1)
      (unitSectionsEquiv _ 1))
  rw [hc, boundary_unit_transport j (unit Z)]
  have hu := Hom.app_presheaf_map (pullbackObjUnitIso j).hom (homOfLE q)
    (pullbackSection j (unitSectionsEquiv (h ⁻¹ᵁ V.1) 1))
  rw [hu]
  change (unit W).presheaf.map (homOfLE q).op
    ((pullbackObjUnitIso j).hom.app (j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
      (pullbackSection j (M := unit Z) (1 : Γ(Z, h ⁻¹ᵁ V.1)))) = _
  rw [pullbackObjUnitIso_hom_app_pullbackSection]
  change W.presheaf.map (homOfLE q).op (j.app (h ⁻¹ᵁ V.1) 1) = 1
  rw [map_one, map_one]

private theorem boundary_tensor_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    (M N : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (t : Γ(N, U)) :
    (boundaryPullbackTensorIso j M N).hom.app (j ⁻¹ᵁ U)
      (((tensorPullbackSectionAdjunction j).unit.app (M ⊗ N)).app U
        (tmulSection s t)) =
      tmulSection (X := X) (M := (tensorPullback j).obj M)
        (N := (tensorPullback j).obj N)
        (((tensorPullbackSectionAdjunction j).unit.app M).app U s)
        (((tensorPullbackSectionAdjunction j).unit.app N).app U t) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((((boundaryPullbackComparison j).app M).hom ⊗ₘ
      ((boundaryPullbackComparison j).app N).hom).app (j ⁻¹ᵁ U))).1
  rw [tensorHom_app_tmulSection, boundary_unit_transport, boundary_unit_transport]
  have hc : (boundaryPullbackTensorIso j M N).hom ≫
      (((boundaryPullbackComparison j).app M).hom ⊗ₘ
        ((boundaryPullbackComparison j).app N).hom) =
      ((boundaryPullbackComparison j).app (M ⊗ N)).hom ≫
        Functor.OplaxMonoidal.δ (pullback j) M N := by
    simp only [boundaryPullbackTensorIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id, tensorHom_id,
      id_whiskerRight, Category.comp_id, Functor.Monoidal.μIso_inv]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, hc, Hom.comp_app,
    ConcreteCategory.comp_apply, boundary_unit_transport]
  exact pullback_δ_app_unit_tmulSection j M N U s t

private theorem power_add_hom {X Y : Scheme.{u}} (j : X ⟶ Y)
    (L : Y.Modules) (m n : ℕ) :
    (tensorPullback j).map (L.tensorPowAddIso m n).inv ≫
      (boundaryPullbackPowIso j L (m + n)).hom =
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).hom ≫
      ((boundaryPullbackPowIso j L m).hom ⊗ₘ
        (boundaryPullbackPowIso j L n).hom) ≫
      (((tensorPullback j).obj L).tensorPowAddIso m n).inv := by
  apply (cancel_epi (((boundaryPullbackPowIso j L m).inv ⊗ₘ
    (boundaryPullbackPowIso j L n).inv) ≫
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).inv)).mp
  simp only [Category.assoc]
  rw [reassoc_of% pullback_power_add]
  simp only [Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]

private theorem evaluate_mul
    {Z S : Scheme.{u}} {h : Z ⟶ S} {L : Z.Modules}
    {A : S.GradedAlgebraData} (ψ : RelativeGradedLineMap h A L)
    {W : Scheme.{u}} (j : W ⟶ Z) (V : S.affineOpens)
    (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    ψ.evaluate j V q (m + n)
      ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (((tensorPullback j).obj L).tensorPowAddIso m n).inv.app ⊤
        (tmulSection (ψ.evaluate j V q m a) (ψ.evaluate j V q n b)) := by
  unfold RelativeGradedLineMap.evaluate
  rw [ψ.mul]
  have hn := congrArg (fun f ↦ f.app (h ⁻¹ᵁ V.1)
    (tmulSection (ψ.component V m a) (ψ.component V n b)))
    ((tensorPullbackSectionAdjunction j).unit_naturality
      (L.tensorPowAddIso m n).inv)
  change (((tensorPullback j).map (L.tensorPowAddIso m n).inv).app
    (j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (((tensorPullbackSectionAdjunction j).unit.app _).app _
      (tmulSection (ψ.component V m a) (ψ.component V n b)))) = _ at hn
  simp only [Hom.comp_app, ConcreteCategory.comp_apply] at hn
  refine (congrArg (fun s ↦ (boundaryPullbackPowIso j L (m + n)).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow (m + n))).presheaf.map
      (homOfLE q).op s)) hn.symm).trans ?_
  have hrmap := Hom.app_presheaf_map
    ((tensorPullback j).map (L.tensorPowAddIso m n).inv) (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app
      (L.tensorPow m ⊗ L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (tmulSection (ψ.component V m a) (ψ.component V n b)))
  rw [← hrmap]
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, power_add_hom]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have hc := Hom.app_presheaf_map
    (boundaryPullbackTensorIso j (L.tensorPow m) (L.tensorPow n)).hom (homOfLE q)
    (((tensorPullbackSectionAdjunction j).unit.app
      (L.tensorPow m ⊗ L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (tmulSection (ψ.component V m a) (ψ.component V n b)))
  rw [hc, boundary_tensor_unit j (L.tensorPow m) (L.tensorPow n)]
  rw [tmulSection_map, tensorHom_app_tmulSection]
  rfl

end AlgebraicGeometry.Scheme.Modules
