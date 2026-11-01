import Langlands.Representation.Aubert.InvolutivityProof
import Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.Smooth.IrreducibleGrothendieckProof

/-!
# Algebraic and supercuspidal boundary cases of segment duality

Involutivity reverses any proposed signed exchange. On a supercuspidal
representation in positive rank, only the one-block term survives in the
actual alternating induction–Jacquet sum.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic SmoothRep

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The supercuspidal boundary of segment duality, for the actual unadjusted
operator and exact finite-length classes in every positive rank. -/
def SupercuspidalEigenvalueStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength), IsSupercuspidal A.representation →
      alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        (-1 : ℤ) ^ (n - 1) • GeneralLinear.finiteLengthClass n F.Carrier A hA

/-- Any signed exchange under the unadjusted Aubert operator gives the reverse
exchange with the same sign. This is conditional on the forward identity. -/
theorem alternatingOperator_signed_reverse (n k : ℕ) :
    letI := T.topology
    ∀ x y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier,
      alternatingOperator F T n x = (-1 : ℤ) ^ k • y →
        alternatingOperator F T n y = (-1 : ℤ) ^ k • x := by
  let := T.topology
  intro x y h
  have hinv : alternatingOperator F T n (alternatingOperator F T n x) = x :=
    LinearMap.congr_fun (involutivity F T n) x
  have hsign : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  calc
    alternatingOperator F T n y =
        (-1 : ℤ) ^ k • ((-1 : ℤ) ^ k • alternatingOperator F T n y) := by
      rw [smul_smul, hsign, one_smul]
    _ = (-1 : ℤ) ^ k • x := by
      congr 1
      rw [h, map_smul] at hinv
      exact hinv

private theorem length_pos_of_rank_pos {n : ℕ} (B : BlockShape n) (hn : 0 < n) :
    0 < B.length := by
  have h := B.toComposition.length_pos_iff.mpr hn
  simpa only [BlockShape.toComposition, Composition.length, List.length_ofFn] using h

/-- A proper standard Jacquet map kills the actual class of a supercuspidal
representation, retaining the exact finite-length Grothendieck quotient. -/
theorem normalizedJacquetK0_supercuspidal {n : ℕ} (B : BlockShape n)
    (hB : B.parabolic F.Carrier ≠ ⊤) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength), IsSupercuspidal A.representation →
      normalizedJacquetK0 F T B (GeneralLinear.finiteLengthClass n F.Carrier A hA) = 0 := by
  let := T.topology
  intro A hA hsc
  have : Subsingleton ((T.normalizedJacquetFunctor B).obj A).obj := by
    change Subsingleton (B.JacquetModule A.representation)
    exact ((CuspidalSupport.standardJacquetSupercuspidalityClause T n
      A.obj A.representation).mp hsc).2 B hB
  have hJ := normalizedJacquetK0_hasFiniteLength F T B A hA
  rw [normalizedJacquetK0_finiteLengthClass F T B A hA hJ]
  exact IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton _ hJ

/-- In positive rank, an actual finite-length supercuspidal representation is
an eigenvector of the unadjusted operator with sign `(-1)^(n-1)`. -/
theorem alternatingOperator_supercuspidal {n : ℕ} (hn : 0 < n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength), IsSupercuspidal A.representation →
      alternatingOperator F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        (-1 : ℤ) ^ (n - 1) • GeneralLinear.finiteLengthClass n F.Carrier A hA := by
  let := T.topology
  classical
  intro A hA hsc
  let : Fintype (BlockShape n) := Fintype.ofFinite _
  let C : BlockShape n := (BlockShape.cutEquiv n).symm ∅
  have hC : C.cuts = ∅ := BlockShape.cuts_cutEquiv_symm _
  have hCl : C.length = 1 := by
    have hc := C.cuts_card
    rw [hC, Finset.card_empty] at hc
    have hp := length_pos_of_rank_pos C hn
    omega
  rw [alternatingOperator_apply]
  rw [Finset.sum_eq_single C]
  · have hwhole := LinearMap.congr_fun
      (inductionJacquetK0_of_cuts_eq_empty F T C hn hC)
      (GeneralLinear.finiteLengthClass n F.Carrier A hA)
    change normalizedInductionK0 F T C
      (normalizedJacquetK0 F T C
        (GeneralLinear.finiteLengthClass n F.Carrier A hA)) = _ at hwhole
    rw [hwhole, hCl, LinearMap.id_apply]
  · intro B _ hBC
    have hB : B.parabolic F.Carrier ≠ ⊤ := by
      intro htop
      have := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top B htop
      have hle : B.length ≤ 1 := by
        simpa only [Fintype.card_fin] using
          (Fintype.card_le_one_iff_subsingleton.mpr (inferInstance : Subsingleton (Fin B.length)))
      have hcuts : B.cuts = ∅ := by
        apply Finset.card_eq_zero.mp
        rw [B.cuts_card]
        omega
      exact hBC (BlockShape.cuts_injective (hcuts.trans hC.symm))
    rw [normalizedJacquetK0_supercuspidal F T B hB A hA hsc, map_zero, smul_zero]
  · simp

/-- The supercuspidal boundary holds without additional theorem premises. -/
theorem supercuspidalEigenvalue : SupercuspidalEigenvalueStatement.{uF, uV} F T := by
  let := T.topology
  intro n hn A hA hsc
  exact alternatingOperator_supercuspidal F T hn A hA hsc

end Langlands.Aubert
