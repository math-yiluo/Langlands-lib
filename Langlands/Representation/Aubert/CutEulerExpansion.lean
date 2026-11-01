import Langlands.Representation.Aubert.FiniteProductGrothendieck
import Langlands.Representation.Geometric.BlockShapeCutCounts
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! The unadjusted Aubert operator as the exact Euler class of the actual cut complex. -/

noncomputable section

namespace Langlands.Aubert.ActualCutComplex

open GeneralLinear SmoothRep
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ}

/-- Cut degree plus one is the actual block length at positive rank. -/
theorem length_eq_cuts_card_add_one (B : BlockShape n) (hn : 0 < n) :
    B.length = B.cuts.card + 1 := by
  have := Langlands.CuspidalSupport.length_pos_of_pos B hn
  have := B.cuts_card
  omega

/-- The explicit cut-indexed shape has length one more than its degree. -/
theorem shape_length (s : Finset (Fin (n - 1))) (hn : 0 < n) :
    (shape (n := n) s).length = s.card + 1 := by
  simpa using length_eq_cuts_card_add_one (shape (n := n) s) hn

/-- A finiteTerm is the actual normalized-functor object used by the Aubert operator. -/
theorem finiteTerm_class (B : BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      FiniteLengthGrothendieckGroup.ofObject (finiteTerm.{uF,uV} F T B A hA) =
        GeneralLinear.finiteLengthClass n F.Carrier
          ((T.normalizedParabolicInductionFunctor.{uF,max uF uV} B).obj
            ((T.normalizedJacquetFunctor.{uF,max uF uV} B).obj A))
          (normalizedInductionJacquet_hasFiniteLength.{uF,uV} F T A hA B) := by
  let := T.topology
  intro A hA
  rfl

/-- The exact signed degree class, including the sole degree at rank zero. -/
def eulerClass :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      A.HasFiniteLength → GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier :=
  letI := T.topology
  fun A hA => ∑ k ∈ Finset.range (n - 1 + 1), ((-1 : ℤ) ^ (n - (k + 1))) •
    FiniteLengthGrothendieckGroup.ofObject (finiteDegree.{uF,uV} F T A hA k)

/-- The actual Aubert operator is the signed sum of the actual complex degrees. -/
theorem alternating_degree_expansion (hn : 0 < n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      alternatingOperator.{uF,uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ (n - (k + 1))) •
          FiniteLengthGrothendieckGroup.ofObject (finiteDegree.{uF,uV} F T A hA k) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let : Fintype (BlockShape n) := Fintype.ofFinite (BlockShape n)
  intro A hA
  let f : Finset (Fin (n - 1)) → GeneralLinear.FiniteLengthGrothendieckGroup.{uV,uF} n F.Carrier :=
    fun s => ((-1 : ℤ) ^ (n - (s.card + 1))) •
      FiniteLengthGrothendieckGroup.ofObject (finiteTerm.{uF,uV} F T (shape (n := n) s) A hA)
  have hbound : ∀ s : Finset (Fin (n - 1)), s.card ∈ Finset.range n := by
    intro s
    have hcard := s.card_le_univ
    simp only [Fintype.card_fin] at hcard
    exact Finset.mem_range.mpr (by omega)
  have hgroup :
      ∑ k ∈ Finset.range n, ∑ s ∈ Finset.univ.filter (fun s => s.card = k), f s = ∑ s, f s :=
    Finset.sum_fiberwise_of_maps_to (fun s _ => hbound s) f
  calc
    alternatingOperator.{uF,uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        ∑ B : BlockShape n, ((-1 : ℤ) ^ (n - B.length)) •
          FiniteLengthGrothendieckGroup.ofObject (finiteTerm.{uF,uV} F T B A hA) := by
      rw [alternatingOperator_finiteLengthClass]
      apply Finset.sum_congr rfl
      intro B _
      rw [finiteTerm_class]
    _ = ∑ s, f s := by
      apply Fintype.sum_equiv (BlockShape.cutEquiv n)
      intro B
      simp only [f, shape, BlockShape.cutEquiv_apply, BlockShape.cutEquiv_symm_cuts]
      rw [← length_eq_cuts_card_add_one B hn]
    _ = ∑ k ∈ Finset.range n, ∑ s ∈ Finset.univ.filter (fun s => s.card = k), f s := hgroup.symm
    _ = ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ (n - (k + 1))) •
        FiniteLengthGrothendieckGroup.ofObject (finiteDegree.{uF,uV} F T A hA k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_subtype
        (p := fun s : Finset (Fin (n - 1)) => s.card = k)
        (Finset.univ.filter (fun s : Finset (Fin (n - 1)) => s.card = k)) (by simp) f,
        degree_class.{uF,uV} F T k A hA, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [f, s.property]

/-- The exact degree Euler class agrees with the unadjusted operator at positive rank. -/
theorem alternating_eq_eulerClass (hn : 0 < n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.HasFiniteLength),
      alternatingOperator.{uF,uV} F T n (GeneralLinear.finiteLengthClass n F.Carrier A hA) =
        eulerClass.{uF,uV} F T A hA := by
  let := T.topology
  intro A hA
  have hn' : n - 1 + 1 = n := by omega
  rw [eulerClass, hn']
  exact alternating_degree_expansion.{uF,uV} F T hn A hA

end Langlands.Aubert.ActualCutComplex
