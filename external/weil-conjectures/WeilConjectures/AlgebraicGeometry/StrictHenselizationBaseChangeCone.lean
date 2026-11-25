/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
import Mathlib.CategoryTheory.Filtered.Connected

/-! # The strict-henselization fibre-product limit cone

Source: Stacks Project, Tag 03Q9, proof: fibre products commute with limits.
(blueprint: lem-weil-pbc-strict-henselization-base-change-cone).
-/

@[expose] public section
universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

/-- The small diagram of ring-written pointed neighbourhoods, forgetting their points.
Source: Stacks Project, Tag 03Q9, affine-neighbourhood limit diagram.
(blueprint: lem-weil-pbc-strict-henselization-base-change-cone). -/
noncomputable def strictHenselizationEtaleDiagram
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) :
    SmallModel.{v} (strictHenselizationNeighbourhoods y) ⥤ Y.Etale :=
  (equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse ⋙
    Functor.Elements.π _ ⋙ AffineEtale.Spec Y

/-- Base change of the affine pointed-neighbourhood diagram has a limiting cone with
vertex the strict-henselization fibre product and the two specified projections.
Source: Stacks Project, Tag 03Q9, proof: fibre products commute with limits.
(blueprint: lem-weil-pbc-strict-henselization-base-change-cone).

Proof: reindex the canonical spectrum cone across the double-opposite equivalence.
The Gamma-Spec unit identifies its diagram with the original affine neighbourhoods.
Transport the limit along that natural isomorphism. Its inverse components are
`Spec.map (ΓSpecIso _).inv`, and the structural-map theorem identifies their composites
with the maps to Y. Lift the two fibre-product projections to every stage; cone
naturality follows by the two projections. Pullback pasting identifies each square
between these legs and the original cone legs as cartesian. Cofilteredness gives
connectedness, and `isLimitOfIsPullbackOfIsConnected` proves the new cone limiting.
The projection formulas are `pullback.lift_fst` and `pullback.lift_snd`. -/
theorem strictHenselizationBaseChangeCone_exists
    {X Y : Scheme.{v}} (f : X ⟶ Y)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    let B := strictHenselizationEtaleDiagram y ⋙
      MorphismProperty.Over.pullback @Etale ⊤ f
    ∃ π : (Functor.const _).obj (pullback (strictHenselizationStructuralMap y) f) ⟶
      (B ⋙ Etale.forget X ⋙ Over.forget X),
      Nonempty (IsLimit (Cone.mk _ π)) ∧
      (∀ j, π.app j ≫ (B.obj j).hom =
        pullback.snd (strictHenselizationStructuralMap y) f) ∧
      (∀ j, π.app j ≫ pullback.fst
          ((strictHenselizationEtaleDiagram y).obj j).hom f =
        pullback.fst (strictHenselizationStructuralMap y) f ≫
          (strictHenselizationCone y).π.app (op (op j)) ≫
            Spec.map (ΓSpecIso
              ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
                j).1.left.unop).inv) := by
  classical
  let A := strictHenselizationEtaleDiagram y
  let D := A ⋙ Etale.forget Y ⋙ Over.forget Y
  have hAff (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      IsAffine (D.obj j) := by
    change IsAffine (Spec _)
    infer_instance
  let _ : ∀ j, IsAffine (D.obj j) := hAff
  let E := (opOpEquivalence (SmallModel.{v} (strictHenselizationNeighbourhoods y))).symm
  let cR := (strictHenselizationCone y).whisker E.functor
  let α : D ⟶ E.functor ⋙ (strictHenselizationAffineDiagram y).op ⋙ Scheme.Spec :=
    Functor.whiskerLeft D ΓSpec.adjunction.unit
  let hIso (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      IsIso (α.app j) := by
    let : IsAffine (D.obj j) := hAff j
    exact inferInstanceAs (IsIso (ΓSpec.adjunction.unit.app (D.obj j)))
  let : IsIso α := NatIso.isIso_of_isIso_app α
  let e := asIso α
  let cY := (Cone.postcompose e.inv).obj cR
  have hcY : IsLimit cY :=
    (IsLimit.postcomposeInvEquiv e _).symm
      ((strictHenselization_properties y).2.2.some.whiskerEquivalence E)
  have hleg (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      cY.π.app j = (strictHenselizationCone y).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso
          ((equivSmallModel.{v} (strictHenselizationNeighbourhoods y)).inverse.obj
            j).1.left.unop).inv := by
    dsimp [cY, cR]
    change _ ≫ (inv α).app j = _
    rw [NatIso.isIso_inv_app]
    change _ ≫ inv (D.obj j).toSpecΓ = _
    congr 1
    change (Spec _).isoSpec.inv = _
    exact isoSpec_Spec_inv _
  have hq (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
      cY.π.app j ≫ (A.obj j).hom = strictHenselizationStructuralMap y := by
    rw [hleg]
    exact Classical.choose_spec (exists_strictHenselizationStructuralMap y) j
  let B := A ⋙ MorphismProperty.Over.pullback @Etale ⊤ f
  let π : (Functor.const _).obj (pullback (strictHenselizationStructuralMap y) f) ⟶
      B ⋙ Etale.forget X ⋙ Over.forget X :=
    { app := fun j ↦ pullback.lift
        (pullback.fst (strictHenselizationStructuralMap y) f ≫ cY.π.app j)
        (pullback.snd (strictHenselizationStructuralMap y) f)
        (by rw [Category.assoc, hq]; exact pullback.condition)
      naturality := by
        intro j k a
        dsimp
        rw [Category.id_comp]
        change pullback.lift _ _ _ = pullback.lift _ _ _ ≫ pullback.lift _ _ _
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
          have hw := cY.w a
          change cY.π.app j ≫
            (MorphismProperty.Over.forget @Etale ⊤ Y ⋙ Over.forget Y).map
              (A.map a) = cY.π.app k at hw
          rw [MorphismProperty.Over.forget_comp_forget_map] at hw
          simpa only [Category.assoc] using
            congrArg (fun g ↦ pullback.fst (strictHenselizationStructuralMap y) f ≫ g)
              hw.symm
        · simp only [Category.assoc, pullback.lift_snd] }
  refine ⟨π, ?_, ?_, ?_⟩
  · let := (strictHenselization_properties y).2.1
    let := IsCofiltered.isConnected
      (C := SmallModel.{v} (strictHenselizationNeighbourhoods y))
    let δ : (B ⋙ Etale.forget X ⋙ Over.forget X) ⟶ D :=
      { app := fun j ↦ pullback.fst (A.obj j).hom f
        naturality := by
          intro j k a
          change pullback.lift _ _ _ ≫ pullback.fst (A.obj k).hom f =
            pullback.fst (A.obj j).hom f ≫ (A.map a).left
          simp only [pullback.lift_fst] }
    let g : (Cone.postcompose δ).obj (Cone.mk _ π) ⟶ cY :=
      { hom := pullback.fst (strictHenselizationStructuralMap y) f
        w := by
          intro j
          change pullback.fst (strictHenselizationStructuralMap y) f ≫ cY.π.app j =
            pullback.lift _ _ _ ≫ pullback.fst (A.obj j).hom f
          rw [pullback.lift_fst] }
    have hs (j : SmallModel.{v} (strictHenselizationNeighbourhoods y)) :
        IsPullback (π.app j) g.hom (δ.app j) (cY.π.app j) := by
      change IsPullback (π.app j) (pullback.fst (strictHenselizationStructuralMap y) f)
        (pullback.fst (A.obj j).hom f) (cY.π.app j)
      apply IsPullback.of_right _ (by dsimp [π]; simp only [pullback.lift_fst])
        (IsPullback.of_hasPullback (A.obj j).hom f).flip
      simpa only [π, pullback.lift_snd, hq] using
        (IsPullback.of_hasPullback (strictHenselizationStructuralMap y) f).flip
    exact ⟨isLimitOfIsPullbackOfIsConnected δ (Cone.mk _ π) cY g hs hcY⟩
  · intro j
    exact pullback.lift_snd _ _ _
  · intro j
    simpa only [π, pullback.lift_fst, hleg] using
      (pullback.lift_fst
        (pullback.fst (strictHenselizationStructuralMap y) f ≫ cY.π.app j)
        (pullback.snd (strictHenselizationStructuralMap y) f)
        (by rw [Category.assoc, hq]; exact pullback.condition))


end AlgebraicGeometry.Scheme
