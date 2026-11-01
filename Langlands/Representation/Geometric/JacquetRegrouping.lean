import Langlands.Representation.Geometric.JacquetPieceGrothendieck
import Langlands.Representation.Geometric.PointwiseJacquetCoefficientProof
import Langlands.Representation.Geometric.RefinementSolomonCoefficients

/-! Fixed-permutation regrouping of actual geometric pieces after restriction. -/

noncomputable section

namespace Langlands.Geometric

open GeneralLinear CuspidalSupport Parabolic

universe uF uV uM

variable {n : ℕ}

/-- With actual target intersection refinements, the signed sum of values
depending on the permutation and target refinement has only the reversed-block
permutation as a survivor. -/
theorem jacquetRefinementSignedSum_eq
    (F : Type uF) [CommRing F] [Nontrivial F] (B : BlockShape n)
    (R : ∀ C : BlockShape n, MinimalRepresentatives C B → BlockRefinement B)
    (hR : ∀ C w, sourceLevi F B C w.val⁻¹ = refinedLevi F B (R C w))
    {M : Type uM} [AddCommGroup M]
    (f : Equiv.Perm (Fin n) → BlockRefinement B → M)
    [Fintype (BlockRefinement B)] :
    letI : Fintype (BlockShape n) := Fintype.ofFinite _
    letI (C : BlockShape n) : Fintype (MinimalRepresentatives C B) := Fintype.ofFinite _
    (∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) •
      ∑ w : MinimalRepresentatives C B, f w.val (R C w)) =
        ∑ Q : BlockRefinement B, (-1 : ℤ) ^ Aubert.refinementSignExponent B Q •
          f B.reversePermutation Q := by
  classical
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives C B) := Fintype.ofFinite _
  let a (C : BlockShape n) (w : Equiv.Perm (Fin n)) (Q : BlockRefinement B) : ℤ :=
    if IsMinimalRepresentative C B w ∧
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w⁻¹).toMonoidHom =
        blockWeyl (B.flatten Q)
    then (-1 : ℤ) ^ (n - C.length) else 0
  have hfiber (C : BlockShape n) (w : MinimalRepresentatives C B)
      (Q : BlockRefinement B) :
      blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w.val⁻¹).toMonoidHom =
        blockWeyl (B.flatten Q) ↔ R C w = Q := by
    rw [← blockWeyl_flatten_eq_intersection F B C w.val⁻¹ (R C w) (hR C w)]
    exact (blockWeyl_flatten_injective B).eq_iff
  have hC (C : BlockShape n) :
      (-1 : ℤ) ^ (n - C.length) •
          ∑ w : MinimalRepresentatives C B, f w.val (R C w) =
        ∑ w : Equiv.Perm (Fin n), ∑ Q : BlockRefinement B, a C w Q • f w Q := by
    rw [Finset.smul_sum]
    apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
    · intro w hw
      have hnot : ¬ IsMinimalRepresentative C B w := by
        intro h
        exact hw ⟨⟨w, h⟩, rfl⟩
      simp [a, hnot]
    · intro w
      simp only [a, w.property, true_and, hfiber C w]
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hCoeff (w : Equiv.Perm (Fin n)) (Q : BlockRefinement B) :
      (∑ C : BlockShape n, a C w Q) =
        if w = B.reversePermutation
        then (-1 : ℤ) ^ Aubert.refinementSignExponent B Q else 0 := by
    simpa only [a, Aubert.refinementSignExponent_eq, BlockShape.flatten] using
      pointwiseJacquetCoefficientStatement n B (B.flatten Q) w
        (ProductLeviMinimalIndex.blockWeyl_flatten_le B Q)
  calc
    _ = ∑ C : BlockShape n, ∑ w : Equiv.Perm (Fin n),
        ∑ Q : BlockRefinement B, a C w Q • f w Q :=
      Finset.sum_congr rfl fun C _ => hC C
    _ = ∑ w : Equiv.Perm (Fin n), ∑ Q : BlockRefinement B,
        (∑ C : BlockShape n, a C w Q) • f w Q := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finset.sum_comm]
      simp only [Finset.sum_smul]
    _ = ∑ w : Equiv.Perm (Fin n), ∑ Q : BlockRefinement B,
        (if w = B.reversePermutation
          then (-1 : ℤ) ^ Aubert.refinementSignExponent B Q else 0) • f w Q := by
      simp_rw [hCoeff]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun Q _ => ?_
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A uniform actual map for a permutation and target refinement. If no
standard source Levi is conjugate to the flattened target, its value is zero.
When one exists, source uniqueness removes the choice. -/
def canonicalJacquetGeometricTerm (B : BlockShape n) (R : BlockRefinement B)
    (w : Equiv.Perm (Fin n)) :
    letI := T.topology
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  classical
  let := T.topology
  exact if h : ∃ K : BlockShape n, ConjugatesLevi (F := F.Carrier) K (B.flatten R) w
    then jacquetGeometricTerm.{uF, uV} F T h.choose B R w h.choose_spec
    else 0

/-- Every actual witness computes the canonical term. -/
theorem canonicalJacquetGeometricTerm_eq (K B : BlockShape n) (R : BlockRefinement B)
    (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) K (B.flatten R) w) :
    canonicalJacquetGeometricTerm.{uF, uV} F T B R w =
      jacquetGeometricTerm.{uF, uV} F T K B R w hw := by
  classical
  let := T.topology
  unfold canonicalJacquetGeometricTerm
  rw [dite_eq_left ⟨K, hw⟩]
  exact jacquetGeometricTerm_eq.{uF, uV} F T _ K B R w _ hw

/-- Regrouping the actual geometric-piece maps after source Jacquet restriction
gives the intrinsic refinement sum at the single surviving outer reversal. -/
theorem geometricPieces_comp_jacquet_signedSum
    (B : BlockShape n)
    (S : ∀ C : BlockShape n, MinimalRepresentatives C B → BlockRefinement C)
    (R : ∀ C : BlockShape n, MinimalRepresentatives C B → BlockRefinement B)
    (hS : ∀ C w, sourceLevi F.Carrier C B w.val = refinedLevi F.Carrier C (S C w))
    (hR : ∀ C w, sourceLevi F.Carrier B C w.val⁻¹ = refinedLevi F.Carrier B (R C w))
    [Fintype (BlockRefinement B)] :
    letI := T.topology
    letI : Fintype (BlockShape n) := Fintype.ofFinite _
    letI (C : BlockShape n) : Fintype (MinimalRepresentatives C B) := Fintype.ofFinite _
    (∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) •
      ∑ w : MinimalRepresentatives C B,
        (geometricPieceK0.{uF, uV} F T C B w.val (S C w) (R C w) (hS C w) (hR C w)).comp
          (normalizedJacquetK0.{uF, uV} F T C)) =
      ∑ Q : BlockRefinement B, (-1 : ℤ) ^ Aubert.refinementSignExponent B Q •
        canonicalJacquetGeometricTerm.{uF, uV} F T B Q B.reversePermutation := by
  classical
  let := T.topology
  let _ : Fintype (BlockShape n) := Fintype.ofFinite _
  let _ (C : BlockShape n) : Fintype (MinimalRepresentatives C B) := Fintype.ofFinite _
  calc
    _ = ∑ C : BlockShape n, (-1 : ℤ) ^ (n - C.length) •
        ∑ w : MinimalRepresentatives C B,
          canonicalJacquetGeometricTerm.{uF, uV} F T B (R C w) w.val := by
      refine Finset.sum_congr rfl fun C _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [geometricPieceK0_comp_jacquetK0.{uF, uV} F T C B w.val
        (S C w) (R C w) (hS C w) (hR C w)]
      exact (canonicalJacquetGeometricTerm_eq.{uF, uV} F T _ B (R C w) w.val
        (conjugatesLevi_flattened_intersections F.Carrier C B w.val
          (S C w) (R C w) (hS C w) (hR C w))).symm
    _ = _ := jacquetRefinementSignedSum_eq F.Carrier B R hR
      (fun w Q => canonicalJacquetGeometricTerm.{uF, uV} F T B Q w)

end Langlands.Geometric
