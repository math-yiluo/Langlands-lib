import Langlands.Representation.Geometric.RefinedCoarseCentralEvaluation
import Langlands.Representation.Classification.SegmentEdgeJacquetReduction

/-! actual inverse-conjugation restriction behind geometric-piece evaluation. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CategoryTheory
open Langlands.Classification.SegmentEdge

universe uR uF uV

/-- Inverse matrix conjugation between the actual refined intersection Levis. -/
def inverseRefinedIntersectionHom
    (R₀ : Type uR) [CommRing R₀] {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi R₀ B C w = refinedLevi R₀ B S)
    (hR : sourceLevi R₀ C B w⁻¹ = refinedLevi R₀ C R) :
    refinedLevi R₀ C R →* refinedLevi R₀ B S :=
  (MulEquiv.subgroupCongr hS.symm).symm.toMonoidHom.comp
    ((intersectionLeviConjugation R₀ B C w).symm.toMonoidHom.comp
      (MulEquiv.subgroupCongr hR).symm.toMonoidHom)

/-- The inverse restriction is actual inverse permutation-matrix conjugation. -/
theorem inverseRefinedIntersectionHom_embedding
    (R₀ : Type uR) [CommRing R₀] {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi R₀ B C w = refinedLevi R₀ B S)
    (hR : sourceLevi R₀ C B w⁻¹ = refinedLevi R₀ C R)
    (m : refinedLevi R₀ C R) :
    B.leviEmbedding R₀ (inverseRefinedIntersectionHom R₀ B C w S R hS hR m).val =
      (permutation n R₀ w)⁻¹ * C.leviEmbedding R₀ m.val * permutation n R₀ w := by
  change B.leviEmbedding R₀
    ((intersectionLeviConjugation R₀ B C w).symm
      ((MulEquiv.subgroupCongr hR).symm m)).val = _
  exact intersectionLeviConjugation_symm_embedding R₀ B C w _

/-- Target coarse scalars, restricted through actual inverse conjugation. -/
def inverseCoarseScalarIntersectionHom
    (R₀ : Type uR) [CommRing R₀] {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi R₀ B C w = refinedLevi R₀ B S)
    (hR : sourceLevi R₀ C B w⁻¹ = refinedLevi R₀ C R) :
    (Fin C.length → R₀ˣ) →* refinedLevi R₀ B S :=
  (inverseRefinedIntersectionHom R₀ B C w S R hS hR).comp
    (coarseScalarRefinedLevi C R R₀)

theorem inverseCoarseScalarIntersectionHom_embedding
    (R₀ : Type uR) [CommRing R₀] {n : ℕ} (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
    (hS : sourceLevi R₀ B C w = refinedLevi R₀ B S)
    (hR : sourceLevi R₀ C B w⁻¹ = refinedLevi R₀ C R)
    (a : Fin C.length → R₀ˣ) :
    B.leviEmbedding R₀ (inverseCoarseScalarIntersectionHom R₀ B C w S R hS hR a).val =
      (permutation n R₀ w)⁻¹ * C.blockScalar R₀ a * permutation n R₀ w := by
  rw [inverseCoarseScalarIntersectionHom, MonoidHom.comp_apply,
    inverseRefinedIntersectionHom_embedding, coarseScalarRefinedLevi_val]
  rfl

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (S : BlockRefinement B) (R : BlockRefinement C)
  (hS : sourceLevi F.Carrier B C w = refinedLevi F.Carrier B S)
  (hR : sourceLevi F.Carrier C B w⁻¹ = refinedLevi F.Carrier C R)

set_option maxHeartbeats 1200000 in
/-- The actual middle coefficient action of a geometric piece is the actual
source normalized refined Jacquet action pulled back by inverse conjugation. -/
def geometricPieceCoefficientEquiv :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
    let J := (T.normalizedRefinedJacquetFunctor B S).obj A
    let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
    let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
    let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
    Q'.representation.Equiv
      ((T.normalizedRefinedJacquet B S A.representation).comp
        (inverseRefinedIntersectionHom F.Carrier B C w S R hS hR)) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro A
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  let ψ := (MulEquiv.subgroupCongr hS.symm).symm.toMonoidHom
  have eJ' : J'.representation.Equiv (J.representation.comp ψ) :=
    subgroupEqualityCompEquiv _ _ hS.symm J J.representation (MonoidHom.id _)
      (Representation.Equiv.refl _)
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  have eQ : Q.representation.Equiv
      (J.representation.comp (ψ.comp (intersectionLeviConjugation F.Carrier B C w).symm.toMonoidHom)) :=
    Representation.Equiv.mk eJ'.toLinearEquiv (fun m =>
      eJ'.isIntertwining' ((intersectionLeviConjugation F.Carrier B C w).symm m))
  exact subgroupEqualityCompEquiv _ _ hR Q J.representation
    (ψ.comp (intersectionLeviConjugation F.Carrier B C w).symm.toMonoidHom) eQ

set_option maxHeartbeats 1200000 in
/-- An actual coarse generalized character of an actual geometric piece
reflects to its source normalized refined Jacquet action along the actual
inverse-conjugated coarse scalar homomorphism. -/
theorem geometricPiece_coarse_character_reflects :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (χ : (Fin C.length → F.Carrierˣ) →* ℂˣ),
    IsGeneralizedEigencharacter
      ((((geometricPieceFunctor T B C w S R hS hR).obj A).ρ).comp
        (C.blockScalarLevi F.Carrier)) χ →
    IsGeneralizedEigencharacter
      ((T.normalizedRefinedJacquet B S A.representation).comp
        (inverseCoarseScalarIntersectionHom F.Carrier B C w S R hS hR)) χ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A χ hχ
  let J := (T.normalizedRefinedJacquetFunctor B S).obj A
  let J' := (subgroupEqualityFunctor _ _ hS.symm).obj J
  let Q := (intersectionTransportFunctor F.Carrier B C w).obj J'
  let Q' := (subgroupEqualityFunctor _ _ hR).obj Q
  have href := T.normalizedRefinedInduced_coarse_character_reflects C R
    Q'.representation χ hχ
  let e := geometricPieceCoefficientEquiv T B C w S R hS hR A
  let ec : Representation.Equiv
      (Q'.representation.comp (coarseScalarRefinedLevi C R F.Carrier))
      ((T.normalizedRefinedJacquet B S A.representation).comp
        (inverseCoarseScalarIntersectionHom F.Carrier B C w S R hS hR)) :=
    Representation.Equiv.mk e.toLinearEquiv
      (fun a => e.isIntertwining' (coarseScalarRefinedLevi C R F.Carrier a))
  exact (isGeneralizedEigencharacter_iff_of_equiv ec χ).mp href

end Langlands.Geometric
