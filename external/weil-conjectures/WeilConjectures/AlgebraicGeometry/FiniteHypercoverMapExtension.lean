/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverTruncation
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStageExtensionWithTruncation
import WeilConjectures.AlgebraicGeometry.EtaleHypercoverProduct
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
/-! # Extending a finite simplicial map after a finite split refinement -/
@[expose] public section
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- A map on finite skeleta extends after a refinement that retains the source skeleton.
Source: Stacks 0DAV, relative replacement. Map the source skeleton to the product
of the two full hypercovers, using the identity in its first factor and the given
finite map in its second. Extend this replacement stage and project to the factors.
(auxiliary; not a blueprint node) -/
theorem exists_refinement_extending_finite_map
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : FiniteSplitEtaleHypercover X) (r : ℕ)
    (t : (SimplicialObject.truncation r).obj U.simplicial ⟶
      (SimplicialObject.truncation r).obj V.simplicial) :
    ∃ (W : FiniteSplitEtaleHypercover X) (a : W.Refinement U) (b : W.Refinement V)
      (e : (SimplicialObject.truncation r).obj W.simplicial ≅
        (SimplicialObject.truncation r).obj U.simplicial),
      (SimplicialObject.truncation r).map a = e.hom ∧
        (SimplicialObject.truncation r).map b = e.hom ≫ t := by
  have hypercover (T : FiniteSplitEtaleHypercover X) : IsEtaleHypercover T.simplicial := by
    intro n
    exact ⟨T.matching n, T.projection n, T.matchingMap n,
      T.projection_naturality n, T.matching_universal n,
      T.matchingMap_projection n, T.matching_cover n⟩
  let K := U.simplicial ⨯ V.simplicial
  have hK : IsEtaleHypercover K :=
    isEtaleHypercover_prod X U.simplicial V.simplicial (hypercover U) (hypercover V)
  let : PreservesLimitsOfShape (Discrete WalkingPair)
      (SimplicialObject.truncation (C := X.Etale) r) := by
    dsimp only [SimplicialObject.truncation]
    infer_instance
  let P := prodComparison (SimplicialObject.truncation r) U.simplicial V.simplicial
  let : IsIso P := by dsimp only [P]; infer_instance
  let R : FiniteSplitReplacementStage K r :=
    { U := U.finiteTruncation r
      f := prod.lift (𝟙 _) t ≫ inv P }
  have hfst : R.f ≫ (SimplicialObject.truncation r).map prod.fst = 𝟙 _ := by
    dsimp only [R]
    simp only [Category.assoc, inv_prodComparison_map_fst, prod.lift_fst, P]
  have hsnd : R.f ≫ (SimplicialObject.truncation r).map prod.snd = t := by
    dsimp only [R]
    simp only [Category.assoc, inv_prodComparison_map_snd, P]
    exact prod.lift_snd _ _
  obtain ⟨W, f, e, hf⟩ := exists_extension_of_replacement_stage K hK r R
  refine ⟨W, f ≫ prod.fst, f ≫ prod.snd, e, ?_, ?_⟩
  · rw [Functor.map_comp, hf]
    rw [Category.assoc, hfst, Category.comp_id]
  · rw [Functor.map_comp, hf]
    rw [Category.assoc, hsnd]

end AlgebraicGeometry.FiniteSplitEtaleHypercover
