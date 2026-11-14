import Langlands.GroupScheme.IntegralModel.ConnectedGenerationFieldPoints
import Langlands.GroupScheme.UnitSubgroup

/-! # Closed subgroups representing generated rational-point images -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ConnectedGenerationField

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
  (a : ∀ j, A j ⟶ G)

/-- A finite family of smooth connected affine groups generates exactly the
rational-point image of a smooth connected closed subgroup. -/
theorem exists_generated_subfamily_points
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
      ConnectedSpace (A j).X.left) (s : Finset I) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left ∧
        IsClosedSubgroup i ∧
        (rationalPoints.map i).range = ⨆ j ∈ s, (rationalPoints.map (a j)).range := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Grp.trivial (Over (Spec (CommRingCat.of k))), kernelUnit G, ?_, ?_, ?_,
      kernelUnit_isClosedSubgroup G, ?_⟩
    · change Smooth (𝟙 (Spec (CommRingCat.of k)))
      infer_instance
    · change IsAffineHom (𝟙 (Spec (CommRingCat.of k)))
      infer_instance
    · change ConnectedSpace (Spec (CommRingCat.of k))
      infer_instance
    · simp only [Finset.notMem_empty, iSup_false, iSup_bot]
      apply le_antisymm ?_ bot_le
      rintro x ⟨y, rfl⟩
      change y ≫ (kernelUnit G).hom.hom = 1
      rw [toUnit_unique y (toUnit _)]
      rfl
  | @insert t s _ ih =>
    obtain ⟨H, i, hsm, haff, hconn, hi, hiRange⟩ := ih
    let : Smooth H.X.hom := hsm
    let : IsAffineHom H.X.hom := haff
    let : ConnectedSpace H.X.left := hconn
    let : Smooth (A t).X.hom := (hA t).1
    let : IsAffineHom (A t).X.hom := (hA t).2.1
    let : ConnectedSpace (A t).X.left := (hA t).2.2
    have hgeom := smoothConnectedAffineGeometry.2 k H (A t) hsm haff hconn
      (hA t).1 (hA t).2.1 (hA t).2.2
    let f : H.X ⊗ (A t).X ⟶ G.X :=
      (fst H.X (A t).X ≫ i.hom.hom) * (snd H.X (A t).X ≫ (a t).hom.hom)
    let v₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X ⊗ (A t).X := lift 1 1
    have hv₀ : v₀ ≫ f = 1 := by
      simp [v₀, f, MonObj.comp_mul, MonObj.one_comp]
    obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
      (H.X ⊗ (A t).X) hgeom.1 hgeom.2.1 hgeom.2.2.2 v₀ f hv₀
    let : GeometricallyConnected D.group.X.hom := hD.2.2.1
    have hDconn : ConnectedSpace D.group.X.left :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
    let bH : H.X ⟶ D.group.X := lift (𝟙 H.X) 1 ≫ D.factor
    have hbH : bH ≫ D.inclusion.hom.hom = i.hom.hom := by
      rw [Category.assoc, D.factor_comp]
      simp [f, MonObj.comp_mul, MonObj.one_comp]
    let bt : (A t).X ⟶ D.group.X := lift 1 (𝟙 (A t).X) ≫ D.factor
    have hbt : bt ≫ D.inclusion.hom.hom = (a t).hom.hom := by
      rw [Category.assoc, D.factor_comp]
      simp [f, MonObj.comp_mul, MonObj.one_comp]
    let U : Subgroup (rationalPoints G) :=
      ⨆ j ∈ insert t s, (rationalPoints.map (a j)).range
    have hIU : (rationalPoints.map i).range ≤ U := by
      rw [hiRange]
      exact iSup_le fun j => iSup_le fun hj =>
        le_iSup_of_le j (le_iSup_of_le (Finset.mem_insert_of_mem hj) le_rfl)
    have htU : (rationalPoints.map (a t)).range ≤ U :=
      le_iSup_of_le t (le_iSup_of_le (Finset.mem_insert_self _ _) le_rfl)
    refine ⟨D.group, D.inclusion, hD.1, hD.2.1, hDconn, D.closed, le_antisymm ?_ ?_⟩
    · let : IsAffineHom (H.X ⊗ (A t).X).hom := hgeom.1
      let : LocallyOfFiniteType (H.X ⊗ (A t).X).hom := hgeom.2.1
      let : GeometricallyIntegral (H.X ⊗ (A t).X).hom := hgeom.2.2.2
      apply generatedImage_range_le D hD U
      intro b
      dsimp only [f]
      rw [MonObj.comp_mul]
      apply U.mul_mem
      · apply hIU
        refine ⟨b ≫ fst _ _, ?_⟩
        change (b ≫ fst _ _) ≫ i.hom.hom = _
        exact Category.assoc _ _ _
      · apply htU
        refine ⟨b ≫ snd _ _, ?_⟩
        change (b ≫ snd _ _) ≫ (a t).hom.hom = _
        exact Category.assoc _ _ _
    · apply iSup_le
      intro j
      apply iSup_le
      intro hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · obtain ⟨y, rfl⟩ := hx
        exact ⟨y ≫ bt, by change (y ≫ bt) ≫ _ = _; rw [Category.assoc, hbt]; rfl⟩
      · have hx' : x ∈ (rationalPoints.map i).range := by
          rw [hiRange]
          have hjle : (rationalPoints.map (a j)).range ≤
              ⨆ j ∈ s, (rationalPoints.map (a j)).range :=
            le_iSup_of_le j (le_iSup_of_le hj le_rfl)
          exact hjle hx
        obtain ⟨y, rfl⟩ := hx'
        exact ⟨y ≫ bH, by change (y ≫ bH) ≫ _ = _; rw [Category.assoc, hbH]; rfl⟩

/-- The closed subgroup for all indices of a finite family. -/
theorem exists_generated_points [Fintype I]
    (hA : ∀ j, Smooth (A j).X.hom ∧ IsAffineHom (A j).X.hom ∧
      ConnectedSpace (A j).X.left) :
    ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      Smooth H.X.hom ∧ IsAffineHom H.X.hom ∧ ConnectedSpace H.X.left ∧
        IsClosedSubgroup i ∧
        (rationalPoints.map i).range = ConnectedGeneration.generatedImages a := by
  classical
  simpa only [Finset.mem_univ, iSup_pos, ConnectedGeneration.generatedImages] using
    exists_generated_subfamily_points a hA Finset.univ

end Langlands.GroupScheme.ConnectedGenerationField
