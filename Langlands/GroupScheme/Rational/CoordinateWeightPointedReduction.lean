import Langlands.GroupScheme.Rational.CoordinateWeightDecompositionStatement
import Langlands.GroupScheme.Rational.PointedCoordinateDecompositionStatement

/-! # Group coordinate weight decomposition from the pointed case

The coordinate and augmentation conclusions for an actual automorphic action are the
pointed affine conclusions for the action that forgets the group law of the target.
The cotangent conclusions follow from the augmentation decomposition, independence of
the cotangent weight spaces, and weight preservation by the quotient map. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CoordinateWeights

section Transfer

/-- An internal decomposition pushed through a surjective linear map into an
independent family of submodules makes that family internal, and the images are
exactly its members. -/
theorem isInternal_and_map_eq_of_surjective {R ι U Q : Type*} [Ring R] [AddCommGroup U]
    [Module R U] [AddCommGroup Q] [Module R Q] [DecidableEq ι]
    (π : U →ₗ[R] Q) (hπ : Function.Surjective π)
    {W : ι → Submodule R U} {W' : ι → Submodule R Q} (hW : DirectSum.IsInternal W)
    (hind : iSupIndep W') (hmap : ∀ i, (W i).map π ≤ W' i) :
    DirectSum.IsInternal W' ∧ ∀ i, (W i).map π = W' i := by
  have htop : ⨆ i, (W i).map π = ⊤ := by
    rw [← Submodule.map_iSup, hW.submodule_iSup_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.2 hπ]
  refine ⟨(DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top W').2
    ⟨hind, top_le_iff.1 (htop ▸ iSup_mono hmap)⟩, ?_⟩
  exact congrFun ((hind.le_iff_eq_of_iSup_eq_top htop).mp hmap)

end Transfer

open Classical in
/-- The coordinate and augmentation decompositions of an actual automorphic action
of a split torus, obtained from the pointed affine statement applied to the action
that forgets the group law of the target. -/
theorem isInternal_weightSpace_and_augmentationWeightSpace_of_pointed
    (h : PointedCoordinateWeights.PointedCoordinateDecompositionStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G) :
    letI := hAff
    DirectSum.IsInternal (weightSpace b) ∧ DirectSum.IsInternal (augmentationWeightSpace b) :=
  letI := hAff
  h k S hS G.X (PointedCoordinateWeights.PointedAction.ofGroup b)

open Classical in
/-- All four conclusions of the target for one action, from the pointed affine
statement, independence of the cotangent weight spaces, and preservation of each
weight by the quotient map from the augmentation ideal to its cotangent space. -/
theorem coordinateWeightDecomposition_of_pointed
    (h : PointedCoordinateWeights.PointedCoordinateDecompositionStatement.{u})
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G) :
    letI := hAff
    iSupIndep (cotangentWeightSpace b) →
    (∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) ≤ cotangentWeightSpace b χ) →
    DirectSum.IsInternal (weightSpace b) ∧
    DirectSum.IsInternal (augmentationWeightSpace b) ∧
    DirectSum.IsInternal (cotangentWeightSpace b) ∧
    (∀ χ : characterLattice S,
      (augmentationWeightSpace b χ).map (cotangentMk G) = cotangentWeightSpace b χ) := by
  let _ := hAff
  intro hind hmk
  obtain ⟨hW, hA⟩ :=
    isInternal_weightSpace_and_augmentationWeightSpace_of_pointed h k G hAff S hS b
  obtain ⟨hC, hmap⟩ := isInternal_and_map_eq_of_surjective (cotangentMk G)
    (Ideal.toCotangent_surjective (augmentationIdeal G)) hA hind hmk
  exact ⟨hW, hA, hC, hmap⟩

/-- The published target follows from the pointed affine statement together with
cotangent independence and weight preservation by the cotangent quotient map for
every actual automorphic action of a split torus. -/
theorem coordinateWeightDecompositionStatement_of_pointed
    (h : PointedCoordinateWeights.PointedCoordinateDecompositionStatement.{u})
    (hcot : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hAff : IsAffineHom G.X.hom) (S : CommGroupScheme (Spec (CommRingCat.of k))),
      IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp G,
      letI := hAff
      iSupIndep (cotangentWeightSpace b) ∧
      ∀ χ : characterLattice S,
        (augmentationWeightSpace b χ).map (cotangentMk G) ≤ cotangentWeightSpace b χ) :
    CoordinateWeightDecompositionStatement.{u} := by
  intro k _ G hAff S hS b
  exact coordinateWeightDecomposition_of_pointed h k G hAff S hS b
    (hcot k G hAff S hS b).1 (hcot k G hAff S hS b).2

end Langlands.GroupScheme.CoordinateWeights
