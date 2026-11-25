/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LocalizedOrdinary.LocalizedOrdinaryPullbackData
import all WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension

/-! # Coherence of the actual finite and completed coefficient maps

## References

* Stacks Project, Tag 03CB
* Bhatt--Scholze, Remark 6.8.15
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.LocalizedOrdinary

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y)

private theorem finite_comp (n : ℕ) :
    completedFiniteCoefficientMap (h ≫ g) d n =
      (proEtaleRingInverseImageComp h g).hom.app ((pbcAdicRings X d).obj (op n)) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (completedFiniteCoefficientMap g d n) ≫ completedFiniteCoefficientMap h d n := by
  have hc := proEtaleConstantComparison_comp h g
    (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  change proEtaleConstantInverseImageMap (h ≫ g) CommRingCat.{u + 1} _ = _ at hc
  simp only [completedFiniteCoefficientMap, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (pbcLevelConstantComparison Y d n).hom
    (pbcLevelConstantComparison Y d n).inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, hc]
  simp only [Category.assoc]
  simpa only [Functor.comp_map, Category.assoc, proEtaleConstantComparison] using
    congrArg
      (fun a ↦ a ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
            (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1}
          (CommRingCat.of (A ⧸ d.ideal ^ (n + 1))) ≫
        (pbcLevelConstantComparison Z d n).hom)
      ((proEtaleRingInverseImageComp h g).hom.naturality
        (pbcLevelConstantComparison X d n).inv)

private theorem finite_id (n : ℕ) :
    completedFiniteCoefficientMap (𝟙 X) d n =
      (proEtaleRingInverseImageId X).hom.app ((pbcAdicRings X d).obj (op n)) := by
  have hc := proEtaleConstantComparison_id X
    (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))
  change proEtaleConstantInverseImageMap (𝟙 X) CommRingCat.{u + 1} _ = _ at hc
  unfold completedFiniteCoefficientMap
  rw [hc, reassoc_of% (proEtaleRingInverseImageId X).hom.naturality
    (pbcLevelConstantComparison X d n).inv]
  simp only [Iso.inv_hom_id, Category.comp_id]

private theorem projection (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection Y d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (pbcAdicProjection X d n) ≫ completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

private theorem completed_comp :
    completedCoefficientMap (h ≫ g) d =
      (proEtaleRingInverseImageComp h g).hom.app (pbcAdicCompletion X d) ≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (completedCoefficientMap g d) ≫ completedCoefficientMap h d := by
  apply limit.hom_ext
  intro n
  change _ ≫ pbcAdicProjection Z d n.unop = _ ≫ pbcAdicProjection Z d n.unop
  rw [projection, Category.assoc, Category.assoc, projection,
    ← Functor.map_comp_assoc, projection, Functor.map_comp]
  rw [finite_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (proEtaleRingInverseImageComp h g).hom.naturality
    (pbcAdicProjection X d n.unop)]

private theorem completed_id :
    completedCoefficientMap (𝟙 X) d =
      (proEtaleRingInverseImageId X).hom.app (pbcAdicCompletion X d) := by
  apply limit.hom_ext
  intro n
  change _ ≫ pbcAdicProjection X d n.unop = _ ≫ pbcAdicProjection X d n.unop
  rw [projection, finite_id]
  exact (proEtaleRingInverseImageId X).hom.naturality (pbcAdicProjection X d n.unop)

private theorem transitions {b a : ℕᵒᵖ} (q : b ⟶ a) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map ((pbcAdicRings X d).map q) ≫
        completedFiniteCoefficientMap g d a.unop =
      completedFiniteCoefficientMap g d b.unop ≫ (pbcAdicRings Y d).map q := by
  let tX := pbcConstantSystemComparison X d
  let tY := pbcConstantSystemComparison Y d
  have hx := tX.inv.naturality q
  have hy := tY.hom.naturality q
  change (pbcAdicRings X d).map q ≫ (pbcLevelConstantComparison X d a.unop).inv =
    (pbcLevelConstantComparison X d b.unop).inv ≫ (adicLisseRingSystem X d.ideal).map q
    at hx
  change (adicLisseRingSystem Y d.ideal).map q ≫
    (pbcLevelConstantComparison Y d a.unop).hom =
    (pbcLevelConstantComparison Y d b.unop).hom ≫ (pbcAdicRings Y d).map q at hy
  let t : adicLisseRingSystem X d.ideal ⋙
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⟶ adicLisseRingSystem Y d.ideal :=
    NatTrans.ofOpSequence
      (fun n ↦ proEtaleConstantInverseImageMap g CommRingCat.{u + 1}
        (CommRingCat.of (A ⧸ d.ideal ^ (n + 1)))) (by
      intro n
      simp only [Functor.comp_map, adicLisseRingSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact proEtaleConstantInverseImageMap_naturality g _)
  have ht := t.naturality q
  simp only [Functor.comp_map, t, NatTrans.ofOpSequence_app] at ht
  unfold completedFiniteCoefficientMap
  rw [← Functor.map_comp_assoc, hx, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% ht]
  rw [hy]

/-- Finite composition, identity and quotient transitions determine completed
composition and identity by joint monicity of the actual limit projections.
Constant scalar sections are preserved by the specified adjunction unit. -/
theorem localizedOrdinaryCoefficientCoherence
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Z : Scheme.{u}} (g : Y ⟶ X) (h : Z ⟶ Y) : Coefficients l E g h := by
  let d := pbcIntegralDatum l E
  refine ⟨finite_comp d g h, completed_comp d g h, ?_, finite_id d,
    completed_id d, ?_, ?_⟩
  · intro n
    rw [projection, ← Functor.map_comp_assoc, projection, Functor.map_comp]
    simp only [Category.assoc]
  · intro S T f b a q
    exact transitions d f q
  · intro S T f V a
    exact pbcCompletedSection_directImage f d (op V) a

end AlgebraicGeometry.Scheme.LocalizedOrdinary
