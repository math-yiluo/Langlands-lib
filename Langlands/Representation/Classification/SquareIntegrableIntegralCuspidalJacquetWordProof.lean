import Langlands.Representation.Classification.SquareIntegrableIntegralCuspidalJacquetWordStatement
import Langlands.Representation.CuspidalSupport.CuspidalTensorJacquetQuotientProof
import Langlands.Representation.Classification.CuspidalJacquetSubsetGroupingProof
import Langlands.Representation.Classification.IrreducibleBinaryProductCommutationProof
import Langlands.Representation.Classification.AdjacentCuspidalJacquetInterchangeProof
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof
import Langlands.Representation.Classification.SupercuspidalSupport
import Langlands.Representation.Exponents.CuspidalTensorRealPartsProof
import Langlands.Representation.Exponents.SquareIntegrableActualJacquetConeProof
import Langlands.Representation.Exponents.ComplementaryPrefixConeObstructionProof
import Langlands.Representation.Exponents.PermutedCuspidalTensorConeProof

/-! # Actual integral cuspidal Jacquet words for analytic discrete series -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private abbrev RankedCuspidalClass :=
  letI := T.topology
  Σ d : ℕ, SupercuspidalClass.{max uF uV, uF} (F := F.Carrier) (n := d)

private def integerTwist (z : ℤ) : RankedCuspidalClass.{uF,uV} F T →
    RankedCuspidalClass.{uF,uV} F T :=
  letI := T.topology
  fun c => ⟨c.1, T.supercuspidalClassRealPowerTwist c.1 (z : ℝ) c.2⟩

private theorem integerTwist_zero (c : RankedCuspidalClass.{uF,uV} F T) :
    integerTwist F T 0 c = c := by
  rcases c with ⟨d, c⟩
  simp [integerTwist, T.supercuspidalClassRealPowerTwist_zero]

private theorem integerTwist_add (z w : ℤ) (c : RankedCuspidalClass.{uF,uV} F T) :
    integerTwist F T z (integerTwist F T w c) = integerTwist F T (z + w) c := by
  rcases c with ⟨d, c⟩
  simp [integerTwist, T.supercuspidalClassRealPowerTwist_add]

/-- Labels on opposite sides of an integral orbit cannot differ by one twist. -/
private theorem integerOrbit_nonadjacent
    (a b base : RankedCuspidalClass.{uF,uV} F T)
    (ha : ¬ ∃ z : ℤ, a = integerTwist F T z base)
    (hb : ∃ z : ℤ, b = integerTwist F T z base) :
    b ≠ integerTwist F T 1 a ∧ a ≠ integerTwist F T 1 b := by
  obtain ⟨z, rfl⟩ := hb
  constructor
  · intro h
    apply ha
    refine ⟨-1 + z, ?_⟩
    have hh := congrArg (integerTwist F T (-1)) h
    simpa only [integerTwist_add, neg_add_cancel, integerTwist_zero] using hh.symm
  · intro h
    exact ha ⟨1 + z, h.trans (integerTwist_add F T 1 z base)⟩

/-- Complementary grouped cones force every original label into one integral
orbit, using nonadjacent binary irreducibility for cross-orbit pairs. -/
private theorem exists_integral_word_of_permutation_cones
    (hbinary : TwoSupercuspidalNonadjacentProductIrreducible.{uF,max uF uV} F T) :
    letI := T.topology
    ∀ (n : ℕ) (_hn : 0 < n) (B : BlockShape n)
      (π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible → π.IsAdmissible → π.HasFiniteLength →
      ∀ C : ∀ i : Fin B.length,
        SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := B.size i),
      SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
        ((T.normalizedJacquetFunctor B).obj π) →
      ∀ x : Fin B.length → ℝ,
      (∀ e : Equiv.Perm (Fin B.length),
        SmoothRep.IsSubquotient (FiniteTensor.externalSmoothObject (fun i => (C (e i)).obj))
          ((T.normalizedJacquetFunctor (B.permute e)).obj π) →
        Exponents.IsPositiveRootCone (x ∘ e)) →
      ∃ (m : ℕ), 0 < m ∧
        ∃ (A : SupercuspidalRep.{uF,max uF uV} (F := F.Carrier) (n := m)) (w : List ℤ),
          w ≠ [] ∧ IntegralCuspidalJacquetWord F T m n A π w := by
  classical
  let := T.topology
  intro n hn B π hπ hadm hfin C hocc x hcones
  have hlen : 0 < B.length := CuspidalSupport.length_pos_of_pos B hn
  let i₀ : Fin B.length := ⟨0, hlen⟩
  let c : Fin B.length → RankedCuspidalClass.{uF,uV} F T :=
    fun i => ⟨B.size i, (C i).isoClass⟩
  let S : Finset (Fin B.length) := Finset.univ.filter
    (fun i => ∃ z : ℤ, c i = integerTwist F T z (c i₀))
  have memS (i : Fin B.length) :
      i ∈ S ↔ ∃ z : ℤ, c i = integerTwist F T z (c i₀) := by simp [S]
  have hS : S.Nonempty := ⟨i₀, (memS _).mpr ⟨0, (integerTwist_zero F T _).symm⟩⟩
  have pair (i j : Fin B.length)
      (hij : (i ∉ S ∧ j ∈ S) ∨ (i ∈ S ∧ j ∉ S)) :
      ((T.binaryNormalizedProductFunctor (B.size i) (B.size j)).obj
        ((C i).obj, (C j).obj)).IsIrreducible ∧
      Nonempty ((T.binaryNormalizedProductFunctor (B.size i) (B.size j)).obj
        ((C i).obj, (C j).obj) ≅
        (Derivative.generalLinearRankCast T (Nat.add_comm (B.size j) (B.size i))).obj
          ((T.binaryNormalizedProductFunctor (B.size j) (B.size i)).obj
            ((C j).obj, (C i).obj))) := by
    have hnij : c j ≠ integerTwist F T 1 (c i) ∧
        c i ≠ integerTwist F T 1 (c j) := by
      rcases hij with ⟨hi,hj⟩ | ⟨hi,hj⟩
      · exact integerOrbit_nonadjacent F T _ _ _ (fun h => hi ((memS i).mpr h))
          ((memS j).mp hj)
      · exact (integerOrbit_nonadjacent F T _ _ _ (fun h => hj ((memS j).mpr h))
          ((memS i).mp hi)).symm
    have hp := hbinary (B.size i) (B.size j) (B.positive i) (B.positive j)
      (C i) (C j)
      (by simpa only [c, integerTwist, Int.cast_one] using hnij.1)
      (by simpa only [c, integerTwist, Int.cast_one] using hnij.2)
    have hp' : ((T.binaryNormalizedProductFunctor (B.size i) (B.size j)).obj
        ((C i).obj, (C j).obj)).IsIrreducible := by
      simpa only [BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
        F T (B.positive i) (B.positive j)] using hp
    exact ⟨hp', irreducibleBinaryProductCommutation F T (B.size i) (B.size j)
      (B.positive i) (B.positive j) (C i).obj (C j).obj
      (C i).property.1 (C j).property.1 hp'⟩
  have hall : ∀ i : Fin B.length, i ∈ S := by
    intro i
    by_contra hi
    have hSc : Sᶜ.Nonempty := ⟨i, Finset.mem_compl.mpr hi⟩
    obtain ⟨e, he, hE⟩ := cuspidalJacquetSubsetGrouping F T
      (adjacentCuspidalJacquetInterchange F T) n B π hπ hadm hfin C hocc S
      (fun i j hi hj => pair i j (Or.inl ⟨hi,hj⟩))
    obtain ⟨f, hf, hF⟩ := cuspidalJacquetSubsetGrouping F T
      (adjacentCuspidalJacquetInterchange F T) n B π hπ hadm hfin C hocc Sᶜ
      (fun i j hi hj => pair i j (Or.inr
        ⟨by simpa only [Finset.mem_compl, not_not] using hi, Finset.mem_compl.mp hj⟩))
    exact Exponents.complementaryPrefixConeObstruction x S e f hS hSc he hf
      (hcones e hE) (hcones f hF)
  choose z hz using fun i => (memS i).mp (hall i)
  refine ⟨B.size i₀, B.positive i₀, C i₀, List.ofFn z, ?_, B, C, z, rfl, ?_, hocc⟩
  · simpa only [ne_eq, List.ofFn_eq_nil_iff] using Nat.ne_of_gt hlen
  · exact hz

/-- Assemble the original actual cuspidal tensor and its permuted analytic
cones, using the nonadjacent binary criterion. -/
private theorem squareIntegrableIntegralCuspidalJacquetWord_of_binary
    (hbinary : TwoSupercuspidalNonadjacentProductIrreducible.{uF,max uF uV} F T) :
    SquareIntegrableIntegralCuspidalJacquetWordExistence.{uF,uV} F T := by
  classical
  let := T.topology
  intro n hn π hπ hsq
  have hfin : π.HasFiniteLength := by
    have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        π.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hπ
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨inferInstance, inferInstance⟩
  obtain ⟨B, C, hquot⟩ :=
    CuspidalSupport.cuspidalTensorJacquetQuotientExistence F T n hn π hπ
  obtain ⟨t, c, _hu, hc, hnorm, _htensor, _hreal⟩ :=
    cuspidalTensorRealParts F T n B C
  exact exists_integral_word_of_permutation_cones F T hbinary n hn B π
    hπ hsq.isAdmissible hfin C hquot.isSubquotient
    (fun i => -((B.size i : ℝ) * t i))
    (permutedCuspidalTensorCone F T n hn B π hsq C c
      (fun i => -((B.size i : ℝ) * t i)) hc hnorm)

/-- Every positive-rank irreducible analytically square-integrable smooth
representation has an actual nonempty cuspidal Jacquet word on one integral
line. -/
theorem squareIntegrableIntegralCuspidalJacquetWordExistence :
    SquareIntegrableIntegralCuspidalJacquetWordExistence.{uF,uV} F T :=
  squareIntegrableIntegralCuspidalJacquetWord_of_binary F T
    (twoSupercuspidalNonadjacentProductIrreducible.{uF,max uF uV} F T)

end Langlands.Classification
