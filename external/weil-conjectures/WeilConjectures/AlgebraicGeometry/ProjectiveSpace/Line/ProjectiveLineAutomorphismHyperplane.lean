/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.ProjectiveLineAutomorphismOverField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line.ProjectiveLineFibrewiseTrivialDescent

/-! # The hyperplane class under a relative projective-line automorphism

## References

* EGA II, Remark 4.2.7
* Stacks Project, Tag 0B8W
* EGA II, Remark 4.2.7, printed p.75, the tautological-line clause for projective-bundle
  isomorphisms
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory
namespace AlgebraicGeometry.ProjectiveLine

private theorem pic_map_ofIsInvertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Y.Modules) [Scheme.Modules.IsInvertible L] :
    Scheme.Pic.map f (Scheme.Pic.ofIsInvertible L) =
      Scheme.Pic.ofIsInvertible ((Scheme.Modules.pullback f).obj L) := by
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback f).mapIso (Scheme.Pic.ofIsInvertibleIso L)⟩

private theorem exists_baseChange_automorphism {S T : Scheme.{u}} (g : T ⟶ S)
    (a : ProjectiveLine S ≅ ProjectiveLine S)
    (ha : a.hom ≫ (ProjectiveLine S ↘ S) = (ProjectiveLine S ↘ S)) :
    ∃ b : ProjectiveLine T ≅ ProjectiveLine T,
      b.hom ≫ (ProjectiveLine T ↘ T) = (ProjectiveLine T ↘ T) ∧
      b.hom ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g =
        ProjectiveSpace.map (ULift.{u} (Fin 2)) g ≫ a.hom := by
  have hai : a.inv ≫ (ProjectiveLine S ↘ S) = (ProjectiveLine S ↘ S) := by
    rw [Iso.inv_comp_eq, ha]
  let f : ProjectiveLine T ⟶ ProjectiveLine T := ProjectiveSpace.liftBaseChange
    (ProjectiveLine T ↘ T) (ProjectiveSpace.map (ULift.{u} (Fin 2)) g ≫ a.hom)
    (by rw [Category.assoc, ha, ProjectiveSpace.map_over])
  let h : ProjectiveLine T ⟶ ProjectiveLine T := ProjectiveSpace.liftBaseChange
    (ProjectiveLine T ↘ T) (ProjectiveSpace.map (ULift.{u} (Fin 2)) g ≫ a.inv)
    (by rw [Category.assoc, hai, ProjectiveSpace.map_over])
  have hf : f ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g =
      ProjectiveSpace.map (ULift.{u} (Fin 2)) g ≫ a.hom :=
    ProjectiveSpace.liftBaseChange_map _ _ _
  have hh : h ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) g =
      ProjectiveSpace.map (ULift.{u} (Fin 2)) g ≫ a.inv :=
    ProjectiveSpace.liftBaseChange_map _ _ _
  have hfp : f ≫ (ProjectiveLine T ↘ T) = (ProjectiveLine T ↘ T) :=
    ProjectiveSpace.liftBaseChange_over _ _ _
  have hhp : h ≫ (ProjectiveLine T ↘ T) = (ProjectiveLine T ↘ T) :=
    ProjectiveSpace.liftBaseChange_over _ _ _
  have hfh : f ≫ h = 𝟙 _ := by
    apply (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).hom_ext
    · rw [Category.assoc, hh, ← Category.assoc, hf]
      simp
    · rw [Category.assoc, hhp, hfp, Category.id_comp]
  have hhf : h ≫ f = 𝟙 _ := by
    apply (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).hom_ext
    · rw [Category.assoc, hf, ← Category.assoc, hh]
      simp
    · rw [Category.assoc, hfp, hhp, Category.id_comp]
  exact ⟨⟨f, h, hfh, hhf⟩, hfp, hf⟩

/-- A relative projective-line automorphism fixes the hyperplane class modulo base lines.

This is just the change-of-model step, and contains no diagonal,
Cartier ideal, Chern class or integration assertion. -/
theorem automorphism_hyperplane (S : Scheme.{u})
    (a : ProjectiveLine S ≅ ProjectiveLine S)
    (ha : a.hom ≫ (ProjectiveLine S ↘ S) = (ProjectiveLine S ↘ S)) :
    ∃ B : S.Pic,
      Scheme.Pic.map a.hom
          (Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) =
        Scheme.Pic.map (ProjectiveLine S ↘ S) B *
          Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1) := by
  let H : (ProjectiveLine S).Pic := Scheme.Pic.ofIsInvertible
    (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)
  have hbase (s : S) : Scheme.Pic.map
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) (S.fromSpecResidueField s))
      (Scheme.Pic.map a.hom H * H⁻¹) = 1 := by
    let g := S.fromSpecResidueField s
    let j := ProjectiveSpace.map (ULift.{u} (Fin 2)) g
    obtain ⟨b, hb, hbj⟩ := exists_baseChange_automorphism g a ha
    have hj : Scheme.Pic.map j H = Scheme.Pic.ofIsInvertible
        (ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (S.residueField s)) 1) := by
      rw [pic_map_ofIsInvertible]
      exact Scheme.Pic.ofIsInvertible_eq_of_iso
        (ProjectiveSpace.pullbackMapTwistIso (ULift.{u} (Fin 2)) g 1)
    have hbH : Scheme.Pic.map b.hom (Scheme.Pic.map j H) = Scheme.Pic.map j H := by
      rw [hj, pic_map_ofIsInvertible]
      exact Scheme.Pic.ofIsInvertible_eq_of_iso
        (automorphism_twist_one_over_field (S.residueField s) b hb).some
    change Scheme.Pic.map j (Scheme.Pic.map a.hom H * H⁻¹) = 1
    rw [Scheme.Pic.map_mul, ← Scheme.Pic.map_comp, ← hbj, Scheme.Pic.map_comp, hbH]
    change Scheme.Pic.map j H * (Scheme.Pic.mapHom j) H⁻¹ = 1
    rw [map_inv]
    exact mul_inv_cancel _
  obtain ⟨B, hB⟩ := exists_base_class_of_fibrewise_trivial S
    (Scheme.Pic.map a.hom H * H⁻¹) hbase
  refine ⟨B, ?_⟩
  change Scheme.Pic.map a.hom H = Scheme.Pic.map (ProjectiveLine S ↘ S) B * H
  rw [hB, inv_mul_cancel_right]

end AlgebraicGeometry.ProjectiveLine
