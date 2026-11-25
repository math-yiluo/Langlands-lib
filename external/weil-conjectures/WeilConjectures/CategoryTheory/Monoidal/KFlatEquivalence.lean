/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# Monoidal equivalences preserve K-flat complexes

A strong monoidal additive equivalence `G : C ⥤ D` of abelian monoidal categories, preserving the
coproducts defining the tensor product of complexes, sends K-flat cochain complexes to K-flat
cochain complexes when applied degreewise
(`CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_of_isEquivalence`): up to the
comparison isomorphisms `G(K ⊗ M) ≅ G(K) ⊗ G(M)`, tensoring with `G(K)` is `G` of tensoring
with `K`, and `G` preserves and reflects quasi-isomorphisms.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.Functor
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalCategory D]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  [(curriedTensor D).Additive] [∀ (X₁ : D), ((curriedTensor D).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (G : C ⥤ D) [G.Additive] [G.Monoidal] [G.IsEquivalence]
  [∀ j, PreservesColimitsOfShape
    (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]

/-- A strong monoidal equivalence, applied degreewise, preserves K-flat complexes. -/
lemma kFlat_mapHomologicalComplex_obj_of_isEquivalence {K : CochainComplex C ℤ}
    (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat ((G.mapHomologicalComplex (.up ℤ)).obj K) := by
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let δ := OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G
  have hq {M M' : CochainComplex C ℤ} (g : M ⟶ M') :
      HomologicalComplex.quasiIso D (.up ℤ) (Gc.map g) ↔
        HomologicalComplex.quasiIso C (.up ℤ) g := by
    simp only [HomologicalComplex.mem_quasiIso_iff]
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology g G
  have : Gc.IsEquivalence := (G.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  have pre {M M' : CochainComplex D ℤ} (g : M ⟶ M') (hg : HomologicalComplex.quasiIso D _ g) :
      ∃ g₀ : Gc.objPreimage M ⟶ Gc.objPreimage M',
        Gc.map g₀ = (Gc.objObjPreimageIso M).hom ≫ g ≫ (Gc.objObjPreimageIso M').inv ∧
        HomologicalComplex.quasiIso C (.up ℤ) g₀ := by
    refine ⟨Gc.preimage _, Gc.map_preimage _, ?_⟩
    rw [← hq, Gc.map_preimage]
    exact (HomologicalComplex.quasiIso D (.up ℤ)).arrow_mk_iso_iff
      (Arrow.isoMk (Gc.objObjPreimageIso M).symm (Gc.objObjPreimageIso M').symm) |>.1 hg
  refine ⟨fun M M' g hg ↦ ?_, fun M M' g hg ↦ ?_⟩
  · obtain ⟨g₀, hg₀, h₀⟩ := pre g hg
    have h₁ := (hq _).2 (hK.1 _ h₀)
    refine (HomologicalComplex.quasiIso D (.up ℤ)).arrow_mk_iso_iff ?_ |>.1 h₁
    refine Arrow.isoMk (asIso ((δ.app K).app _) ≪≫
        whiskerLeftIso _ (Gc.objObjPreimageIso M))
      (asIso ((δ.app K).app _) ≪≫ whiskerLeftIso _ (Gc.objObjPreimageIso M')) ?_
    have := (δ.app K).naturality g₀
    dsimp at this ⊢
    rw [reassoc_of% this]
    simp only [whiskerLeftIso_hom, Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
    erw [hg₀]
    simp
  · obtain ⟨g₀, hg₀, h₀⟩ := pre g hg
    have h₁ := (hq _).2 (hK.2 _ h₀)
    refine (HomologicalComplex.quasiIso D (.up ℤ)).arrow_mk_iso_iff ?_ |>.1 h₁
    refine Arrow.isoMk (asIso ((δ.app _).app K) ≪≫
        whiskerRightIso (Gc.objObjPreimageIso M) _)
      (asIso ((δ.app _).app K) ≪≫ whiskerRightIso (Gc.objObjPreimageIso M') _) ?_
    have := congr_app (δ.naturality g₀) K
    dsimp at this ⊢
    rw [reassoc_of% this]
    simp only [whiskerRightIso_hom, Category.assoc, ← MonoidalCategory.comp_whiskerRight]
    erw [hg₀]
    simp

end CategoryTheory.Functor
