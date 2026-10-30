import Langlands.Representation.Geometric.WholeLeviPieceTransport
import Langlands.Representation.Parabolic.RefinedOppositeReversal
import Langlands.Representation.Classification.ProductLeviMinimalIndex
import Langlands.Representation.CuspidalSupport.LeviAssociation

/-! Flattened coordinates for inner reversal and opposite whole-target pieces. -/

noncomputable section

namespace Langlands.Geometric.RefinedOppositePieceTransport

open GeneralLinear CuspidalSupport ProductLeviDualOpposite
open RefinedOppositeReversal OppositeCuspidalJacquetFiltration

universe uF uV

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Reverse the inner blocks inside each coarse block. -/
def innerReversePermutation : Equiv.Perm (Fin n) :=
  blockPermOf B (fun i => (S i).reversePermutation)

section Groups

variable (F : Type uF) [Field F]

/-- Inner block relabelling, expressed in the actual flattened product Levis. -/
def flattenedRefinementReverseEquiv :
    (B.flatten S).Levi F ≃* (B.flatten (reverseRefinement B S)).Levi F :=
  (flattenedLeviEquiv F B S).trans
    ((refinedLeviReverseEquiv B S).trans
      (flattenedLeviEquiv F B (reverseRefinement B S)).symm)

/-- The flattened relabelling is inverse conjugation by the assembled inner
reversal permutation. -/
theorem innerReverse_conj_embedding (m : (B.flatten S).Levi F) :
    permutation n F (innerReversePermutation B S) *
        (B.flatten (reverseRefinement B S)).leviEmbedding F
          (flattenedRefinementReverseEquiv B S F m) *
        (permutation n F (innerReversePermutation B S))⁻¹ =
      (B.flatten S).leviEmbedding F m := by
  rw [← flattenedLeviEquiv_embedding]
  simp only [flattenedRefinementReverseEquiv, MulEquiv.trans_apply,
    MulEquiv.apply_symm_apply]
  unfold innerReversePermutation
  rw [← ProductLeviMinimalIndex.leviEmbedding_conj_blockPermOf]
  change B.leviEmbedding F
      (reverseWeyl B S F *
        (refinedLeviReverseEquiv B S (flattenedLeviEquiv F B S m)).val *
        (reverseWeyl B S F)⁻¹) = _
  rw [reverseWeyl_mul_refinedLeviReverseEquiv, flattenedLeviEquiv_embedding]

/-- The assembled reversal conjugates the reversed flattened Levi onto the
original flattened Levi. -/
theorem conjugatesLevi_innerReverse :
    ConjugatesLevi (F := F) (B.flatten (reverseRefinement B S)) (B.flatten S)
      (innerReversePermutation B S) := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨_, ⟨m', rfl⟩, rfl⟩
    refine ⟨(flattenedRefinementReverseEquiv B S F).symm m', ?_⟩
    rw [← innerReverse_conj_embedding, MulEquiv.apply_symm_apply]
    rfl
  · rintro ⟨m, rfl⟩
    refine ⟨(B.flatten (reverseRefinement B S)).leviEmbedding F
      (flattenedRefinementReverseEquiv B S F m), ⟨_, rfl⟩, ?_⟩
    exact innerReverse_conj_embedding B S F m

/-- Actual inverse Levi conjugation is precisely the constructed flattened
inner block relabelling. -/
theorem leviConjugation_innerReverse_symm (m : (B.flatten S).Levi F) :
    (leviConjugation (B.flatten (reverseRefinement B S)) (B.flatten S)
      (innerReversePermutation B S) (conjugatesLevi_innerReverse B S F)).symm m =
        flattenedRefinementReverseEquiv B S F m := by
  apply (B.flatten (reverseRefinement B S)).leviEmbedding_injective F
  rw [leviConjugation_symm_embedding]
  have h := innerReverse_conj_embedding B S F m
  rw [← h]
  group

variable (C : BlockShape n) (x : Equiv.Perm (Fin n))

/-- The upper-piece coordinate after reversing the inner source and the
whole target. -/
def reversedPiecePermutation : Equiv.Perm (Fin n) :=
  C.reversePermutation⁻¹ * (x * innerReversePermutation B S)

theorem reverse_mul_reversedPiecePermutation :
    C.reversePermutation * reversedPiecePermutation B S C x =
      x * innerReversePermutation B S := by
  exact mul_inv_cancel_left _ _

/-- Actual conjugacy of the original fine source gives actual conjugacy of
the reversed fine source to the reversed target. -/
theorem conjugatesLevi_reversedPiece
    (hx : ConjugatesLevi (F := F) (B.flatten S) C x) :
    ConjugatesLevi (F := F) (B.flatten (reverseRefinement B S)) C.reverse
      (reversedPiecePermutation B S C x) :=
  conjugatesLevi_mul (conjugatesLevi_mul (conjugatesLevi_innerReverse B S F) hx)
    (conjugatesLevi_inv (conjugatesLevi_reverse C))

end Groups

section Normalized

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (B.Levi F.Carrier) V)

/-- In flattened coordinates, transport by inner reversal identifies the
reversed upper normalized Jacquet module with the original opposite one. -/
def flattenedNormalizedOppositeReverseEquiv :
    Representation.Equiv
      (transport (B.flatten (reverseRefinement B S)) (B.flatten S)
        (innerReversePermutation B S) (conjugatesLevi_innerReverse B S F.Carrier)
        ((T.normalizedRefinedJacquet B (reverseRefinement B S) ρ).comp
          (flattenedLeviEquiv F.Carrier B (reverseRefinement B S)).toMonoidHom))
      ((T.normalizedRefinedOppositeJacquet B S ρ).comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom) := by
  have h :
      transport (B.flatten (reverseRefinement B S)) (B.flatten S)
          (innerReversePermutation B S) (conjugatesLevi_innerReverse B S F.Carrier)
          ((T.normalizedRefinedJacquet B (reverseRefinement B S) ρ).comp
            (flattenedLeviEquiv F.Carrier B (reverseRefinement B S)).toMonoidHom) =
        ((T.normalizedRefinedJacquet B (reverseRefinement B S) ρ).comp
          (refinedLeviReverseEquiv B S).toMonoidHom).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom := by
    apply MonoidHom.ext
    intro m
    change T.normalizedRefinedJacquet B (reverseRefinement B S) ρ
        (flattenedLeviEquiv F.Carrier B (reverseRefinement B S)
          ((leviConjugation _ _ _ _).symm m)) = _
    rw [leviConjugation_innerReverse_symm]
    simp only [flattenedRefinementReverseEquiv, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply]
    rfl
  rw [h]
  exact FiniteTensorFiltration.compCongr
    (normalizedRefinedOppositeReverseEquiv T B S ρ)
    (flattenedLeviEquiv F.Carrier B S).toMonoidHom

end Normalized

section Piece

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) (C : BlockShape n) (x : Equiv.Perm (Fin n))
  (hx : ConjugatesLevi (F := F.Carrier) (B.flatten S) C x)
  (R : BlockRefinement C.reverse)
  (hS : sourceLevi F.Carrier B C.reverse (reversedPiecePermutation B S C x) =
    refinedLevi F.Carrier B (reverseRefinement B S))
  (hR : sourceLevi F.Carrier C.reverse B (reversedPiecePermutation B S C x)⁻¹ =
    refinedLevi F.Carrier C.reverse R)

set_option maxHeartbeats 1200000 in
/-- The reversed upper whole-target piece, pulled back to the original
target coordinates, is transport of the original inner opposite Jacquet
module. This is a comparison of actual representations. -/
def reversedWholeLeviGeometricPieceEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      Representation.Equiv
        ((((geometricPieceFunctor T B C.reverse (reversedPiecePermutation B S C x)
        (reverseRefinement B S) R hS hR).obj A).ρ).comp
          (leviReverseEquiv C).toMonoidHom)
        (transport (B.flatten S) C x hx
          ((T.normalizedRefinedOppositeJacquet B S A.representation).comp
            (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) := by
  letI := T.topology
  intro A
  let y := reversedPiecePermutation B S C x
  let hy := conjugatesLevi_reversedPiece B S F.Carrier C x hx
  let J := (T.normalizedRefinedJacquet B (reverseRefinement B S)
    A.representation).comp
      (flattenedLeviEquiv F.Carrier B (reverseRefinement B S)).toMonoidHom
  let e := wholeLeviGeometricPieceEquiv T B C.reverse y
    (reverseRefinement B S) R hS hR hy A
  let e' := FiniteTensorFiltration.compCongr e (leviReverseEquiv C).toMonoidHom
  have eTransport :
      Representation.Equiv
        ((transport (B.flatten (reverseRefinement B S)) C.reverse y hy J).comp
          (leviReverseEquiv C).toMonoidHom)
        (transport (B.flatten S) C x hx
          (transport (B.flatten (reverseRefinement B S)) (B.flatten S)
            (innerReversePermutation B S) (conjugatesLevi_innerReverse B S F.Carrier)
            J)) := by
    have eReverse := transportReverseEquiv hy
      (conjugatesLevi_mul hy (conjugatesLevi_reverse C)) J
    have eReverse' : Representation.Equiv
        ((transport (B.flatten (reverseRefinement B S)) C.reverse y hy J).comp
          (leviReverseEquiv C).toMonoidHom)
        (transport (B.flatten (reverseRefinement B S)) C
          (x * innerReversePermutation B S)
          (conjugatesLevi_mul (conjugatesLevi_innerReverse B S F.Carrier) hx) J) := by
      simpa only [y, reversedPiecePermutation, mul_inv_cancel_left] using eReverse
    rw [transport_mul (conjugatesLevi_innerReverse B S F.Carrier) hx] at eReverse'
    exact eReverse'
  exact e'.trans (eTransport.trans
    (transportEquiv x hx
      (flattenedNormalizedOppositeReverseEquiv B S T A.representation)))

end Piece

end Langlands.Geometric.RefinedOppositePieceTransport
