/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointedEtaleSectionCone.PointedEtaleSectionCone
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension

/-! # The small strict-local model as a pointed section cone

Only the model-specific geometric sections and their compatibility are constructed here.
Restriction and its universal property use the general PointedEtaleSectionCone API.

Source: Stacks Project, Tags 03Q9 and 03QO.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

variable {S : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- The geometric section obtained from a limit leg of the small strict-local cone.
Source: Stacks, Tag 03Q9 (blueprint: def-weil-pbc-small-strict-local-section-cone). -/
noncomputable def strictLocalNeighbourhoodSection
    (j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s)) ⟶
      (Scheme.strictHenselizationStructuralMap s).Etale.obj
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1) :=
  MorphismProperty.Over.homMk
    (pullback.lift
      ((Scheme.strictHenselizationCone s).π.app (op (op j)) ≫
        Spec.map (Scheme.ΓSpecIso
          ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j).1.left.unop).inv)
      (𝟙 _)
      (by
        rw [Category.assoc, Category.id_comp]
        exact ((Scheme.exists_strictHenselizationStructuralMap s).choose_spec j)))
    (by
      change _ ≫ pullback.snd _ (Scheme.strictHenselizationStructuralMap s) = _
      simp
      rfl) (by trivial)

/-- The small strict-local cone supplies compatible sections over an initial diagram.
Source: Stacks, Tag 03Q9 (blueprint: def-weil-pbc-small-strict-local-section-cone).
Proof: initiality is strictHenselization_properties. For compatibility, compare both
pullback projections. The base projection is the identity, and the other projection
is natural by the limit-cone equation and naturality of the affine spectrum comparison. -/
noncomputable def strictLocalSectionCone :
    PointedEtaleSectionCone (Scheme.strictHenselizationStructuralMap s)
      ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
        Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
          (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)) where
  initial := (Scheme.strictHenselization_properties s).1
  section_ := strictLocalNeighbourhoodSection s
  naturality {i j} a := by
    let N := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    let t := (Functor.Elements.π (Scheme.pointSmallEtale s).fiber).map (N.map a)
    change strictLocalNeighbourhoodSection s i ≫
      (Scheme.strictHenselizationStructuralMap s).Etale.map t =
        strictLocalNeighbourhoodSection s j
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · rw [MorphismProperty.Comma.comp_left]
      dsimp only [Scheme.Hom.Etale, MorphismProperty.Over.pullback,
        strictLocalNeighbourhoodSection, MorphismProperty.Over.homMk,
        Over.homMk, CostructuredArrow.homMk,
        MorphismProperty.Comma.comp_left]
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      erw [pullback.lift_fst]
      have : IsAffine
          ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).obj
            (N.obj i)).left := by
        change IsAffine (Spec _)
        infer_instance
      have : IsAffine
          ((Functor.Elements.π (Scheme.pointSmallEtale s).fiber).obj
            (N.obj j)).left := by
        change IsAffine (Spec _)
        infer_instance
      have hw := Scheme.isoSpec_inv_naturality t.left
      let Ri := unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1.left
      let Rj := unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj i).1.left
      change Spec.map t.left.appTop ≫ (Spec Ri).isoSpec.inv =
        (Spec Rj).isoSpec.inv ≫ t.left at hw
      simp only [Scheme.isoSpec_Spec_inv] at hw
      erw [← hw, ← Category.assoc]
      exact congrArg (fun z ↦ z ≫ _) ((Scheme.strictHenselizationCone s).w a.op.op)
    · rw [MorphismProperty.Comma.comp_left]
      dsimp only [Scheme.Hom.Etale, MorphismProperty.Over.pullback,
        strictLocalNeighbourhoodSection, MorphismProperty.Over.homMk,
        Over.homMk, CostructuredArrow.homMk,
        MorphismProperty.Comma.comp_left]
      simp only [Category.assoc, pullback.lift_snd]
      erw [pullback.lift_snd]

end AlgebraicGeometry.Etale
