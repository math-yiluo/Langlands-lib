import Langlands.AllField.Representation.RankinSelberg.TemperedTypeLFactorData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualDuality
import Langlands.Representation.RankinSelberg.ReflectionRigidityProof

/-!
# JPSS 1983, Proposition (9.4)(3), for tempered-type data over a nonarchimedean local field

For two data of irreducible tempered blocks with antitone real exponents, the
L-polynomial of the pair of standard modules is the product of the L-polynomials of the
pairs of twisted blocks. The proof is the double induction of JPSS 1983, printed pages
458-462, from the pole bound (8.4) and the tail divisibility (9.3), stated as the
premises `TemperedPoleBoundStatement` and `InducedTailLFactorAt`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg

open Langlands.RankinSelberg (IsOfWhittakerType succBlockShape reflectionRigidity)
open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

section Reflection

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {r t : ℕ}
  (d : TemperedTypeDatum.{uF, uV} (F := F) (r + 1))
  (e : TemperedTypeDatum.{uF, uW} (F := F) (t + 1))

set_option maxHeartbeats 800000 in
/-- Certificates for the reversed inverse-transpose data give the reflected gamma ratio
with the original and dual block products. -/
theorem nonempty_temperedTypeReflectedRatioData
    (c : TemperedTypeLPolynomialData ψ ν d e)
    (cD : TemperedTypeLPolynomialData (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      d.inverseTranspose e.inverseTranspose) :
    Nonempty (Langlands.RankinSelberg.TemperedLFactorGamma.ReflectedRatioData
      (Langlands.AllField.LocalFactor.residueReflection F) c.inducedPolynomial
      cD.inducedPolynomial (∏ i, ∏ j, c.blockPolynomial i j)
      (∏ i, ∏ j, cD.blockPolynomial i j)) := by
  have hPD : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback d.standardModule) (inverseTransposePullback e.standardModule)
      cD.inducedPolynomial :=
    (IsPadicRankLPolynomial.congr_equiv d.inverseTransposeStandardModuleEquiv
      e.inverseTransposeStandardModuleEquiv).mpr cD.induced_spec
  have hQD (i : Fin d.shape.length) (j : Fin e.shape.length) :
      IsPadicRankLPolynomial (ψ.scale (-1)) ν.val
        ((d.twistedBlock i).representation.comp
          (GeneralLinear.inverseTranspose (d.shape.size i) F).toMonoidHom)
        ((e.twistedBlock j).representation.comp
          (GeneralLinear.inverseTranspose (e.shape.size j) F).toMonoidHom)
        (cD.blockPolynomial i.rev j.rev) := by
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    have h := (IsPadicRankLPolynomial.congr_equiv (d.inverseTransposeTwistedBlockEquiv i)
      (e.inverseTransposeTwistedBlockEquiv j)).mpr (cD.block_spec i j)
    simp only [Fin.rev_rev] at h ⊢
    exact h
  have hprod : (∏ i : Fin d.shape.length, ∏ j : Fin e.shape.length,
      cD.blockPolynomial i.rev j.rev) =
      ∏ i, ∏ j, cD.blockPolynomial i j := by
    calc
      _ = ∏ i, ∏ j : Fin e.shape.length, cD.blockPolynomial i j.rev :=
        Equiv.prod_comp Fin.revPerm
          (fun i => ∏ j : Fin e.shape.length, cD.blockPolynomial i j.rev)
      _ = _ := Finset.prod_congr rfl fun i _ =>
        Equiv.prod_comp Fin.revPerm (cD.blockPolynomial i)
  have hc := c.induced_spec
  have hcb := c.block_spec
  revert hPD hQD hc hcb
  rcases d with ⟨⟨k, size, pos, total⟩, τ, hiτ, htτ, hwτ, u, hu⟩
  rcases e with ⟨⟨l, size', pos', total'⟩, σ, hiσ, htσ, hwσ, v, hv⟩
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
  obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
    ⟨fun j => size' j - 1, funext fun j => (Nat.sub_add_cancel (pos' j)).symm⟩
  intro hPD hQD hc hcb
  let π := fun i => ((τ i).twist (determinantPowerCharacter (m i + 1) (u i))
    (isOpen_ker_determinantPowerCharacter (m i + 1) (u i))).representation
  let σ' := fun j => ((σ j).twist (determinantPowerCharacter (n j + 1) (v j))
    (isOpen_ker_determinantPowerCharacter (n j + 1) (v j))).representation
  have hπ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (π i) := fun i =>
    (isOfRankWhittakerType_succ ψ (π i)).mp
      ((isOfRankWhittakerType_twist_iff ψ (τ i).representation (u i)).mpr (hwτ ψ i))
  have hσ : ∀ j, IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (σ' j) := fun j =>
    (isOfRankWhittakerType_succ ψ (σ' j)).mp
      ((isOfRankWhittakerType_twist_iff ψ (σ j).representation (v j)).mpr (hwσ ψ j))
  have hR := TemperedLFactorGamma.nonempty_reflectedRatioData F ψ ν m n total total'
    π σ' hπ hσ c.inducedPolynomial cD.inducedPolynomial c.blockPolynomial
    (fun i j => cD.blockPolynomial i.rev j.rev) hc hcb hPD hQD
  simpa only [hprod] using hR

/-- Original and reversed certified polynomial data, with the reciprocal reflection
identity `D(X) = c X^m E(q⁻¹ / X)` for their normalized residuals. -/
structure TemperedTypeReflectionData where
  original : TemperedTypeLPolynomialData ψ ν d e
  dual : TemperedTypeLPolynomialData (ψ.scale (-1))
    (DominantRankTransport.negatedSelfDualHaar F ψ ν) d.inverseTranspose e.inverseTranspose
  coefficient : ℂˣ
  exponent : ℤ
  identity : algebraMap ℂ[X] (RatFunc ℂ) original.quotient.polynomial =
    (RatFunc.C (coefficient : ℂ) * (RatFunc.X : RatFunc ℂ) ^ exponent) *
      Langlands.LocalFactor.RationalReflection.subst
        (Langlands.AllField.LocalFactor.residueReflection F)
        (algebraMap ℂ[X] (RatFunc ℂ) dual.quotient.polynomial)

/-- The reflected residual identity for two data of positive rank. -/
def temperedTypeReflectionData : TemperedTypeReflectionData ψ ν d e := by
  let c := temperedTypeLPolynomialData ψ ν d e
  let cD := temperedTypeLPolynomialData (ψ.scale (-1))
    (DominantRankTransport.negatedSelfDualHaar F ψ ν) d.inverseTranspose e.inverseTranspose
  let R := Classical.choice (nonempty_temperedTypeReflectedRatioData ψ ν d e c cD)
  refine {
    original := c
    dual := cD
    coefficient := R.coefficient
    exponent := R.exponent
    identity := ?_ }
  have hP : c.inducedPolynomial ≠ 0 := c.induced_spec.ne_zero
  have hPD : cD.inducedPolynomial ≠ 0 := cD.induced_spec.ne_zero
  have hBD : (∏ i, ∏ j, cD.blockPolynomial i j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact (cD.block_spec i j).ne_zero
  exact Langlands.RankinSelberg.TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio
    (Langlands.AllField.LocalFactor.residueReflection F) R.coefficient R.exponent hP hPD hBD
    c.quotient.factorization cD.quotient.factorization R.ratio

end Reflection

section Induction

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

private theorem poleFree_of_dvd {D C : ℂ[X]} {a : ℝ} (hdiv : D ∣ C)
    (hC : ∀ w : ℂ, ‖w‖ < a → C.eval w ≠ 0) :
    ∀ w : ℂ, ‖w‖ < a → D.eval w ≠ 0 := by
  obtain ⟨S, hS⟩ := hdiv
  intro w hw hzero
  apply hC w hw
  rw [hS, eval_mul, hzero, zero_mul]

private theorem standardPairLPolynomial_exists
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n t : ℕ} (hn : 0 < n) (ht : 0 < t)
    (d : TemperedTypeDatum.{uF, uV} (F := F) n) (e : TemperedTypeDatum.{uF, uW} (F := F) t) :
    ∃ P : ℂ[X], IsPadicRankLPolynomial ψ ν.val d.standardModule e.standardModule P := by
  cases n with
  | zero => omega
  | succ n => cases t with
    | zero => omega
    | succ t =>
      exact ⟨(temperedTypeLPolynomialData ψ ν d e).inducedPolynomial,
        (temperedTypeLPolynomialData ψ ν d e).induced_spec⟩

variable (F)

/-- The product formula for all pairs of data with fewer than `N` blocks in total. -/
private def ProductBelow (N : ℕ) : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n t : ℕ}
    (d : TemperedTypeDatum.{uF, uV} (F := F) n) (e : TemperedTypeDatum.{uF, uW} (F := F) t)
    (P : ℂ[X]) (Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]),
    d.shape.length + e.shape.length < N →
    IsPadicRankLPolynomial ψ ν.val d.standardModule e.standardModule P →
    (∀ i j, IsPadicRankLPolynomial ψ ν.val
      (d.twistedBlock i).representation (e.twistedBlock j).representation (Q i j)) →
    P = ∏ i, ∏ j, Q i j

variable {F}

variable (hpole : TemperedPoleBoundStatement.{uF, uV, uW} F)
  (htail₁ : InducedTailLFactorAt.{uF, max uF uV, max uF uV, max uF uW} F)
  (htail₂ : InducedTailLFactorAt.{uF, max uF uW, max uF uW, max uF uV} F)
  (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {r t : ℕ}
  (d : TemperedTypeDatum.{uF, uV} (F := F) (r + 1))
  (e : TemperedTypeDatum.{uF, uW} (F := F) (t + 1))

include htail₂ in
set_option maxHeartbeats 800000 in
private theorem residual_dvd_firstColumn
    (hsmall : ProductBelow.{uF, uV, uW} F (d.shape.length + e.shape.length))
    (c : TemperedTypeLPolynomialData ψ ν d e) :
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
    obtain ⟨Ptail, hPt⟩ := standardPairLPolynomial_exists ψ ν
      (Nat.succ_pos r) (e.shape.tailRank_pos h) d (e.tail h)
    have hQt (i : Fin d.shape.length) (j : Fin (k + 1)) :
        IsPadicRankLPolynomial ψ ν.val (d.twistedBlock i).representation
          ((e.tail h).twistedBlock j).representation
          (c.blockPolynomial i (e.shape.tailIndex h j)) :=
      c.block_spec i (e.shape.tailIndex h j)
    have hprod := hsmall ψ ν d (e.tail h) Ptail
      (fun i j => c.blockPolynomial i (e.shape.tailIndex h j))
      (Nat.add_lt_add_left (e.tail_length_lt h) _) hPt hQt
    have hdiv := TemperedTypeDatum.standardTailLPolynomial_dvd (ψ := ψ) (ν := ν) htail₂ e h
      d.standardModule
      (d.standardModule_rankWhittaker ψ (Nat.succ_pos r))
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
      exact (c.block_spec i (e.shape.tailIndex h j)).ne_zero
    apply residual_dvd_cofactor hA _ hdiv
    have hsplit : (∏ i, ∏ j, c.blockPolynomial i j) =
        (∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t))) * A := by
      simp_rw [prod_head_tail h]
      exact Finset.prod_mul_distrib
    rw [mul_comm, ← hsplit]
    exact c.quotient.factorization

include htail₁ in
set_option maxHeartbeats 800000 in
private theorem residual_dvd_firstRow
    (hsmall : ProductBelow.{uF, uV, uW} F (d.shape.length + e.shape.length))
    (c : TemperedTypeLPolynomialData ψ ν d e) :
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
    obtain ⟨Ptail, hPt⟩ := standardPairLPolynomial_exists ψ ν
      (d.shape.tailRank_pos h) (Nat.succ_pos t) (d.tail h) e
    have hQt (i : Fin (k + 1)) (j : Fin e.shape.length) :
        IsPadicRankLPolynomial ψ ν.val ((d.tail h).twistedBlock i).representation
          (e.twistedBlock j).representation
          (c.blockPolynomial (d.shape.tailIndex h i) j) :=
      c.block_spec (d.shape.tailIndex h i) j
    have hprod := hsmall ψ ν (d.tail h) e Ptail
      (fun i j => c.blockPolynomial (d.shape.tailIndex h i) j)
      (Nat.add_lt_add_right (d.tail_length_lt h) _) hPt hQt
    have hdiv := TemperedTypeDatum.standardTailLPolynomial_dvd (ψ := ψ) (ν := ν) htail₁ d h
      e.standardModule
      (e.standardModule_rankWhittaker ψ (Nat.succ_pos t)) c.induced_spec hPt
    rw [hprod] at hdiv
    let A : ℂ[X] := ∏ i : Fin (k + 1), ∏ j,
      c.blockPolynomial (d.shape.tailIndex h i) j
    have hA : A ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact (c.block_spec (d.shape.tailIndex h i) j).ne_zero
    apply residual_dvd_cofactor hA _ hdiv
    have hsplit : (∏ i, ∏ j, c.blockPolynomial i j) =
        (∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j) * A :=
      prod_head_tail h _
    rw [mul_comm, ← hsplit]
    exact c.quotient.factorization

include hpole in
private theorem blockLPolynomial_poleFree
    (c : TemperedTypeLPolynomialData ψ ν d e)
    (i : Fin d.shape.length) (j : Fin e.shape.length) :
    ∀ w : ℂ,
      ‖w‖ < ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (d.exponent i + e.exponent j) →
        (c.blockPolynomial i j).eval w ≠ 0 :=
  realPowerTwistRankLPolynomial_poleFree hpole (d.shape.positive i) (e.shape.positive j)
    (d.blocks i).representation (e.blocks j).representation
    (d.irreducible i) (d.tempered i) (e.irreducible j) (e.tempered j)
    (d.exponent i) (e.exponent j) (c.block_spec i j)

include hpole in
private theorem firstColumn_poleFree
    (c : TemperedTypeLPolynomialData ψ ν d e) :
    ∀ w : ℂ,
      ‖w‖ < ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (d.exponent (firstIndex d.shape (Nat.succ_pos r)).rev +
          e.exponent (firstIndex e.shape (Nat.succ_pos t))) →
        (∏ i, c.blockPolynomial i (firstIndex e.shape (Nat.succ_pos t))).eval w ≠ 0 := by
  intro w hw
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply blockLPolynomial_poleFree hpole ψ ν d e c i _ w
  apply lt_of_lt_of_le hw
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  · exact add_le_add (d.antitone (le_reverse_first d.shape (Nat.succ_pos r) i)) le_rfl

include hpole in
private theorem firstRow_poleFree
    (c : TemperedTypeLPolynomialData ψ ν d e) :
    ∀ w : ℂ,
      ‖w‖ < ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        (d.exponent (firstIndex d.shape (Nat.succ_pos r)) +
          e.exponent (firstIndex e.shape (Nat.succ_pos t)).rev) →
        (∏ j, c.blockPolynomial (firstIndex d.shape (Nat.succ_pos r)) j).eval w ≠ 0 := by
  intro w hw
  simp only [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  apply blockLPolynomial_poleFree hpole ψ ν d e c _ j w
  apply lt_of_lt_of_le hw
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one.le
  · exact add_le_add le_rfl (e.antitone (le_reverse_first e.shape (Nat.succ_pos t) j))

/-- The reciprocal residue scale `q⁻¹` has norm strictly less than one. -/
theorem norm_residueReflection_lt_one :
    ‖(Langlands.AllField.LocalFactor.residueReflection F : ℂ)‖ < 1 := by
  rw [Langlands.AllField.LocalFactor.coe_residueReflection, norm_inv, Complex.norm_natCast]
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  exact (inv_lt_one₀ (lt_trans zero_lt_one hq)).mpr hq

include hpole htail₁ htail₂ in
set_option maxHeartbeats 800000 in
private theorem reflectedData_product
    (hsmall : ProductBelow.{uF, uV, uW} F (d.shape.length + e.shape.length))
    (R : TemperedTypeReflectionData ψ ν d e) :
    R.original.inducedPolynomial = ∏ i, ∏ j, R.original.blockPolynomial i j := by
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  let s : ℝ := d.exponent (firstIndex d.shape (Nat.succ_pos r)).rev +
    e.exponent (firstIndex e.shape (Nat.succ_pos t))
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast lt_trans Nat.zero_lt_one (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hD := poleFree_of_dvd
    (residual_dvd_firstColumn htail₂ ψ ν d e hsmall R.original)
    (firstColumn_poleFree hpole ψ ν d e R.original)
  have hE := poleFree_of_dvd
    (residual_dvd_firstRow htail₁ (ψ.scale (-1))
      (DominantRankTransport.negatedSelfDualHaar F ψ ν)
      d.inverseTranspose e.inverseTranspose hsmall R.dual)
    (firstRow_poleFree hpole (ψ.scale (-1))
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
  have hgap : ‖(Langlands.AllField.LocalFactor.residueReflection F : ℂ)‖ <
      q ^ s * q ^ (-s) := by
    rw [hab]
    exact norm_residueReflection_lt_one
  obtain ⟨hDone, _⟩ := reflectionRigidity
    (q ^ s) (q ^ (-s)) (Langlands.AllField.LocalFactor.residueReflection F)
    R.coefficient R.exponent
    R.original.quotient.polynomial R.dual.quotient.polynomial
    (Real.rpow_pos_of_pos hq _) (Real.rpow_pos_of_pos hq _) hgap
    R.original.quotient.coeff_zero R.dual.quotient.coeff_zero hD hE R.identity
  simpa only [hDone, one_mul] using R.original.quotient.factorization.symm

include hpole htail₁ htail₂ in
private theorem productBelow_all (N : ℕ) : ProductBelow.{uF, uV, uW} F N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro ψ ν n m d e P Q hlt hP hQ
    have hsmall : ProductBelow.{uF, uV, uW} F (d.shape.length + e.shape.length) :=
      ih _ hlt
    cases n with
    | zero => exact hP.elim
    | succ n => cases m with
      | zero => exact hP.elim
      | succ m =>
        let R := temperedTypeReflectionData ψ ν d e
        calc
          P = R.original.inducedPolynomial := hP.unique R.original.induced_spec
          _ = ∏ i, ∏ j, R.original.blockPolynomial i j :=
            reflectedData_product hpole htail₁ htail₂ ψ ν d e hsmall R
          _ = ∏ i, ∏ j, Q i j := by
            apply Finset.prod_congr rfl
            intro i _
            apply Finset.prod_congr rfl
            intro j _
            exact (R.original.block_spec i j).unique (hQ i j)

end Induction

/-- JPSS 1983, Proposition (9.4)(3) (printed pages 458-462), for data of irreducible
tempered blocks with antitone real exponents over a nonarchimedean local field `F`, from
the pole bound (8.4) and the tail divisibility (9.3) over `F`: the certified L-polynomial
of the two standard modules is the product of the certified L-polynomials of the pairs of
twisted blocks. -/
theorem temperedTypeLPolynomial_product
    (hpole : TemperedPoleBoundStatement.{uF, uV, uW} F)
    (htail₁ : InducedTailLFactorAt.{uF, max uF uV, max uF uV, max uF uW} F)
    (htail₂ : InducedTailLFactorAt.{uF, max uF uW, max uF uW, max uF uV} F)
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {n t : ℕ} (d : TemperedTypeDatum.{uF, uV} (F := F) n)
    (e : TemperedTypeDatum.{uF, uW} (F := F) t)
    {P : ℂ[X]} {Q : Fin d.shape.length → Fin e.shape.length → ℂ[X]}
    (hP : IsPadicRankLPolynomial ψ ν.val d.standardModule e.standardModule P)
    (hQ : ∀ i j, IsPadicRankLPolynomial ψ ν.val
      (d.twistedBlock i).representation (e.twistedBlock j).representation (Q i j)) :
    P = ∏ i, ∏ j, Q i j :=
  productBelow_all hpole htail₁ htail₂ (d.shape.length + e.shape.length + 1) ψ ν d e P Q
    (Nat.lt_succ_self _) hP hQ

end Langlands.AllField.RankinSelberg
