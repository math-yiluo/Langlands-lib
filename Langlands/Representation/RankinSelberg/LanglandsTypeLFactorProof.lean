import Langlands.Representation.RankinSelberg.LanglandsTypeReflectionData
import Langlands.Representation.RankinSelberg.AnalyticTemperedTwistLPolynomialData
import Langlands.Representation.RankinSelberg.SegmentHeadLFactorReduction

/-! The block-product formula for genuine Langlands standard modules. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial
open PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance typeProductTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance typeProductValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance typeProductLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

private theorem blockLength_pos {n : ℕ} (B : BlockShape n) (hn : 0 < n) :
    0 < B.length := by
  by_contra h
  have hz : B.length = 0 := by omega
  have hs := B.sum_eq
  have hempty : IsEmpty (Fin B.length) := ⟨fun i => by have := i.isLt; omega⟩
  let := hempty
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hs
  omega

private def firstIndex {n : ℕ} (B : BlockShape n) (hn : 0 < n) : Fin B.length :=
  ⟨0, blockLength_pos B hn⟩

private theorem le_reverse_first {n : ℕ} (B : BlockShape n) (hn : 0 < n)
    (i : Fin B.length) : i ≤ (firstIndex B hn).rev := by
  change i.val ≤ B.length - 1 - 0
  have := i.isLt
  omega

private theorem prod_head_tail {α : Type*} [CommMonoid α] {n k : ℕ}
    (h : n = k + 2) (f : Fin n → α) :
    (∏ i, f i) = f (Fin.cast h.symm 0) *
      ∏ j : Fin (k + 1), f (Fin.cast h.symm j.succ) := by
  rw [← Equiv.prod_comp (finCongr h.symm) f]
  exact Fin.prod_univ_succ _

private theorem residual_dvd_cofactor {A C D P : ℂ[X]} (hA : A ≠ 0)
    (hprod : A * C = D * P) (hdiv : A ∣ P) : D ∣ C := by
  obtain ⟨S, rfl⟩ := hdiv
  refine ⟨S, mul_left_cancel₀ hA ?_⟩
  rw [hprod]
  ring

private theorem standardPairLPolynomial_exists
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData n)
    (e : TemperedLanglandsDatum.{uW,uF} F.canonicalTopologicalData t) :
    ∃ P : ℂ[X], IsPadicRankLPolynomial F ψ ν.val
      d.standardModule.representation e.standardModule.representation P := by
  cases n with
  | zero => omega
  | succ n => cases t with
    | zero => omega
    | succ t =>
      let c := langlandsTypeLPolynomialData F ψ ν d e
      exact ⟨c.inducedPolynomial, c.induced_spec⟩

private theorem standardTailLPolynomial_dvd_rank
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n t k : ℕ}
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData n)
    (h : d.shape.length = k + 2)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (Langlands.GeneralLinear t F.Carrier) W)
    (hσ : IsOfPadicRankWhittakerType F ψ σ) {P Ptail : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val d.standardModule.representation σ P)
    (htail : IsPadicRankLPolynomial F ψ ν.val
      (d.tail h).standardModule.representation σ Ptail) : Ptail ∣ P := by
  cases n with
  | zero => exact hP.elim
  | succ n => cases t with
    | zero => exact hσ.elim
    | succ t => exact langlandsStandardTailLPolynomial_dvd F ψ ν d h σ hσ hP htail

private def ProductBelow (N : ℕ) : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n t : ℕ}
    (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData n)
    (e : TemperedLanglandsDatum.{uW,uF} F.canonicalTopologicalData t)
    (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
    d.shape.length + e.shape.length < N →
    IsPadicRankLPolynomial F ψ ν.val
      d.standardModule.representation e.standardModule.representation P →
    (∀ i j, IsPadicRankLPolynomial F ψ ν.val
      (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation
      (F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation
      (Q i j)) →
    P = ∏ i, ∏ j, Q i j

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ}
  (d : TemperedLanglandsDatum.{uV,uF} F.canonicalTopologicalData (r + 1))
  (e : TemperedLanglandsDatum.{uW,uF} F.canonicalTopologicalData (t + 1))

set_option maxHeartbeats 800000 in
private theorem residual_dvd_firstColumn
    (hsmall : ProductBelow.{uF,uV,uW} F (d.shape.length + e.shape.length))
    (c : LanglandsTypeLPolynomialData F ψ ν d e) :
    c.quotient.polynomial ∣
      ∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t)) := by
  by_cases h1 : e.shape.length = 1
  · have hB : (∏ i, ∏ j, c.blockPolynomial i j) =
        ∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t)) := by
      apply Finset.prod_congr rfl
      intro i _
      have hall (j : Fin e.shape.length) : j = firstIndex e.shape (Nat.succ_pos t) := by
        apply Fin.ext
        have := j.isLt
        change j.val = 0
        omega
      rw [Finset.prod_eq_single (firstIndex e.shape (Nat.succ_pos t))]
      · intro j _ hj
        exact (hj (hall j)).elim
      · simp
    rw [← hB]
    exact ⟨c.inducedPolynomial, c.quotient.factorization⟩
  · obtain ⟨k, h⟩ : ∃ k, e.shape.length = k + 2 := by
      have := blockLength_pos e.shape (Nat.succ_pos t)
      exact ⟨e.shape.length - 2, by omega⟩
    obtain ⟨Ptail, hPt⟩ := standardPairLPolynomial_exists F ψ ν
      (Nat.succ_pos r) (e.shape.tailRank_pos h) d (e.tail h)
    have hQt (i : Fin d.shape.length) (j : Fin (k + 1)) :
        IsPadicRankLPolynomial F ψ ν.val
          (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation
          (F.canonicalTopologicalData.twistedBlocks
            (e.tail h).shape (e.tail h).blocks (e.tail h).exponent j).representation
          (c.blockPolynomial i (e.shape.tailIndex h j)) :=
      c.block_spec i (e.shape.tailIndex h j)
    have hprod := hsmall ψ ν d (e.tail h) Ptail
      (fun i j => c.blockPolynomial i (e.shape.tailIndex h j))
      (Nat.add_lt_add_left (e.tail_length_lt h) _) hPt hQt
    have hdiv := standardTailLPolynomial_dvd_rank F ψ ν e h
      d.standardModule.representation c.left_type
      ((isPadicRankLPolynomial_comm _ _ _).mp c.induced_spec)
      ((isPadicRankLPolynomial_comm _ _ _).mp hPt)
    rw [hprod] at hdiv
    let A : ℂ[X] := ∏ i, ∏ j : Fin (k + 1),
      c.blockPolynomial i (e.shape.tailIndex h j)
    have hA : A ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact fun hz => by simpa [hz] using
        (c.block_spec i (e.shape.tailIndex h j)).coeff_zero
    apply residual_dvd_cofactor hA _ hdiv
    have hsplit : (∏ i, ∏ j, c.blockPolynomial i j) =
        (∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t))) * A := by
      simp_rw [prod_head_tail h]
      exact Finset.prod_mul_distrib
    rw [mul_comm, ← hsplit]
    exact c.quotient.factorization

set_option maxHeartbeats 800000 in
private theorem residual_dvd_firstRow
    (hsmall : ProductBelow.{uF,uV,uW} F (d.shape.length + e.shape.length))
    (c : LanglandsTypeLPolynomialData F ψ ν d e) :
    c.quotient.polynomial ∣
      ∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j := by
  by_cases h1 : d.shape.length = 1
  · have hB : (∏ i, ∏ j, c.blockPolynomial i j) =
        ∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j := by
      have hall (i : Fin d.shape.length) : i = firstIndex d.shape (Nat.succ_pos r) := by
        apply Fin.ext
        have := i.isLt
        change i.val = 0
        omega
      rw [Finset.prod_eq_single (firstIndex d.shape (Nat.succ_pos r))]
      · intro i _ hi
        exact (hi (hall i)).elim
      · simp
    rw [← hB]
    exact ⟨c.inducedPolynomial, c.quotient.factorization⟩
  · obtain ⟨k, h⟩ : ∃ k, d.shape.length = k + 2 := by
      have := blockLength_pos d.shape (Nat.succ_pos r)
      exact ⟨d.shape.length - 2, by omega⟩
    obtain ⟨Ptail, hPt⟩ := standardPairLPolynomial_exists F ψ ν
      (d.shape.tailRank_pos h) (Nat.succ_pos t) (d.tail h) e
    have hQt (i : Fin (k + 1)) (j : Fin e.shape.length) :
        IsPadicRankLPolynomial F ψ ν.val
          (F.canonicalTopologicalData.twistedBlocks
            (d.tail h).shape (d.tail h).blocks (d.tail h).exponent i).representation
          (F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation
          (c.blockPolynomial (d.shape.tailIndex h i) j) :=
      c.block_spec (d.shape.tailIndex h i) j
    have hprod := hsmall ψ ν (d.tail h) e Ptail
      (fun i j => c.blockPolynomial (d.shape.tailIndex h i) j)
      (Nat.add_lt_add_right (d.tail_length_lt h) _) hPt hQt
    have hdiv := standardTailLPolynomial_dvd_rank F ψ ν d h
      e.standardModule.representation c.right_type c.induced_spec hPt
    rw [hprod] at hdiv
    let A : ℂ[X] := ∏ i : Fin (k + 1), ∏ j,
      c.blockPolynomial (d.shape.tailIndex h i) j
    have hA : A ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact fun hz => by simpa [hz] using
        (c.block_spec (d.shape.tailIndex h i) j).coeff_zero
    apply residual_dvd_cofactor hA _ hdiv
    have hsplit : (∏ i, ∏ j, c.blockPolynomial i j) =
        (∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j) * A :=
      prod_head_tail h _
    rw [mul_comm, ← hsplit]
    exact c.quotient.factorization

private theorem analyticTemperedTwistRankLPolynomial_poleFree
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear m F.Carrier) W)
    (hiπ : Representation.IsIrreducible π)
    (htπ : F.canonicalTopologicalData.IsTempered π)
    (hiσ : Representation.IsIrreducible σ)
    (htσ : F.canonicalTopologicalData.IsTempered σ)
    (s z : ℝ) {P : ℂ[X]}
    (hP : IsPadicRankLPolynomial F ψ ν.val
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm n) s π)
      (realPowerTwist (F.canonicalTopologicalData.determinantNorm m) z σ) P) :
    ∀ w : ℂ,
      ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^ (s + z) →
        P.eval w ≠ 0 := by
  cases n with
  | zero => omega
  | succ n => cases m with
    | zero => omega
    | succ m =>
      exact analyticTemperedTwistLPolynomial_poleFree F ψ ν π σ hiπ htπ hiσ htσ s z hP

private theorem blockLPolynomial_poleFree
    (c : LanglandsTypeLPolynomialData F ψ ν d e)
    (i : Fin d.shape.length) (j : Fin e.shape.length) :
    ∀ w : ℂ,
      ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (d.exponent i + e.exponent j) →
        (c.blockPolynomial i j).eval w ≠ 0 :=
  analyticTemperedTwistRankLPolynomial_poleFree F ψ ν
    (d.shape.positive i) (e.shape.positive j)
    (d.blocks i).representation (e.blocks j).representation
    (d.irreducible i) (d.tempered i) (e.irreducible j) (e.tempered j)
    (d.exponent i) (e.exponent j) (c.block_spec i j)

private theorem firstColumn_poleFree
    (c : LanglandsTypeLPolynomialData F ψ ν d e) :
    ∀ w : ℂ,
      ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (d.exponent (firstIndex d.shape (Nat.succ_pos r)).rev +
          e.exponent (firstIndex e.shape (Nat.succ_pos t))) →
        (∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t))).eval w ≠ 0 := by
  intro w hw
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply blockLPolynomial_poleFree F ψ ν d e c i _ w
  apply lt_of_lt_of_le hw
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  · exact add_le_add (d.strictAnti.antitone
      (le_reverse_first d.shape (Nat.succ_pos r) i)) le_rfl

private theorem firstRow_poleFree
    (c : LanglandsTypeLPolynomialData F ψ ν d e) :
    ∀ w : ℂ,
      ‖w‖ < (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (d.exponent (firstIndex d.shape (Nat.succ_pos r)) +
          e.exponent (firstIndex e.shape (Nat.succ_pos t)).rev) →
        (∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j).eval w ≠ 0 := by
  intro w hw
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply blockLPolynomial_poleFree F ψ ν d e c _ j w
  apply lt_of_lt_of_le hw
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  · exact add_le_add le_rfl (e.strictAnti.antitone
      (le_reverse_first e.shape (Nat.succ_pos t) j))

private theorem poleFree_of_dvd {D C : ℂ[X]} {a : ℝ} (hdiv : D ∣ C)
    (hC : ∀ w : ℂ, ‖w‖ < a → C.eval w ≠ 0) :
    ∀ w : ℂ, ‖w‖ < a → D.eval w ≠ 0 := by
  obtain ⟨S, hS⟩ := hdiv
  intro w hw hzero
  apply hC w hw
  rw [hS, eval_mul, hzero, zero_mul]

set_option maxHeartbeats 800000 in
private theorem reflectedData_product
    (hsmall : ProductBelow.{uF,uV,uW} F (d.shape.length + e.shape.length))
    (R : LanglandsTypeReflectionData F ψ ν d e) :
    R.original.inducedPolynomial = ∏ i, ∏ j, R.original.blockPolynomial i j := by
  let q : ℝ := F.canonicalTopologicalData.residueCardinality
  let s : ℝ := d.exponent (firstIndex d.shape (Nat.succ_pos r)).rev +
    e.exponent (firstIndex e.shape (Nat.succ_pos t))
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast lt_trans Nat.zero_lt_one
      F.canonicalTopologicalData.residueCardinality_gt_one
  have hD := poleFree_of_dvd
    (residual_dvd_firstColumn F ψ ν d e hsmall R.original)
    (firstColumn_poleFree F ψ ν d e R.original)
  have hE := poleFree_of_dvd
    (residual_dvd_firstRow F (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      d.inverseTranspose e.inverseTranspose hsmall R.dual)
    (firstRow_poleFree F (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      d.inverseTranspose e.inverseTranspose R.dual)
  have hexp :
      d.inverseTranspose.exponent
          (firstIndex d.inverseTranspose.shape (Nat.succ_pos r)) +
        e.inverseTranspose.exponent
          (firstIndex e.inverseTranspose.shape (Nat.succ_pos t)).rev = -s := by
    change -d.exponent (firstIndex d.shape (Nat.succ_pos r)).rev +
      -e.exponent (firstIndex e.shape (Nat.succ_pos t)).rev.rev = -s
    rw [Fin.rev_rev]
    dsimp only [s]
    ring
  rw [hexp] at hE
  have hab : q ^ s * q ^ (-s) = 1 := by
    rw [← Real.rpow_add hq]
    simp
  have hgap : ‖(LocalFactor.residueReflection F : ℂ)‖ < q ^ s * q ^ (-s) := by
    rw [hab]
    exact TemperedLFactorAlgebra.norm_residueReflection_lt_one F
  obtain ⟨hDone, _⟩ := reflectionRigidity
    (q ^ s) (q ^ (-s)) (LocalFactor.residueReflection F) R.coefficient R.exponent
    R.original.quotient.polynomial R.dual.quotient.polynomial
    (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hq _) hgap
    R.original.quotient.coeff_zero R.dual.quotient.coeff_zero hD hE R.identity
  simpa only [hDone, one_mul] using R.original.quotient.factorization.symm

private theorem productBelow_all (N : ℕ) : ProductBelow.{uF,uV,uW} F N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ψ ν n m d e P Q hlt hP hQ
    have hsmall : ProductBelow.{uF,uV,uW} F (d.shape.length + e.shape.length) :=
      ih _ hlt
    cases n with
    | zero => exact hP.elim
    | succ n => cases m with
      | zero => exact hP.elim
      | succ m =>
        let R := langlandsTypeReflectionData F ψ ν d e
        calc
          P = R.original.inducedPolynomial := hP.unique R.original.induced_spec
          _ = ∏ i, ∏ j, R.original.blockPolynomial i j :=
            reflectedData_product F ψ ν d e hsmall R
          _ = ∏ i, ∏ j, Q i j := by
            apply Finset.prod_congr rfl
            intro i _
            apply Finset.prod_congr rfl
            intro j _
            exact (R.original.block_spec i j).unique (hQ i j)

variable {F ψ ν d e}

/-- The certified standard-module polynomial is the product of the certified
twisted-block polynomials. -/
theorem langlandsTypeLPolynomial_product
    {P : ℂ[X]} {Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      d.standardModule.representation e.standardModule.representation P)
    (hQ : ∀ i j, IsPadicRankLPolynomial F ψ ν.val
      (F.canonicalTopologicalData.twistedBlocks d.shape d.blocks d.exponent i).representation
      (F.canonicalTopologicalData.twistedBlocks e.shape e.blocks e.exponent j).representation
      (Q i j)) :
    P = ∏ i, ∏ j, Q i j :=
  productBelow_all F (d.shape.length + e.shape.length + 1) ψ ν d e P Q
    (Nat.lt_succ_self _) hP hQ

/-- JPSS Proposition 9.4(3): existence, complete certificates and the block
product for the actual Langlands standard modules. -/
theorem langlandsTypeLFactor : LanglandsTypeLFactorStatement.{uF,uV,uW} := by
  intro p hp F ψ ν r t d e
  let c := langlandsTypeLPolynomialData F ψ ν d e
  exact ⟨c.inducedPolynomial, c.blockPolynomial, c.induced_spec, c.block_spec,
    langlandsTypeLPolynomial_product c.induced_spec c.block_spec⟩

end Langlands.RankinSelberg
