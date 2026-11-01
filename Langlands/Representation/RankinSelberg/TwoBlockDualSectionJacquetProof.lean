import Langlands.Representation.RankinSelberg.TwoBlockDualSectionJacquetStatement
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.Induction.InverseTranspose
import Mathlib.MeasureTheory.Measure.Haar.Unique

noncomputable section

set_option maxHeartbeats 1000000

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators NNReal

namespace TwoBlockDualSectionJacquet

universe uF uW

section Carrier

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
variable (sigma : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))

private theorem reversedShape :
    (succBlockShape m h).reverse = succBlockShape (fun i => m i.rev)
      ((Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h) := rfl

private theorem reverse_index (i : Fin 2)
    (a : Fin ((succBlockShape m h).reverse.size i)) :
    ((succBlockShape m h).reverse.index i a).rev =
      (succBlockShape m h).index i.rev a.rev := by
  have hh := TwoBlockJacquet.blockRanks_add h
  fin_cases i
  · change ((succBlockShape (fun i => m i.rev)
      ((Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h)).index 0 a).rev =
      (succBlockShape m h).index 1 a.rev
    erw [TwoBlockJacquet.index_zero, TwoBlockJacquet.index_one]
    apply Fin.ext
    change t + 1 - (a.val + 1) = m 0 + 1 + (m 1 + 1 - (a.val + 1))
    have ha : a.val < m 1 + 1 := a.isLt
    omega
  · change ((succBlockShape (fun i => m i.rev)
      ((Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h)).index 1 a).rev =
      (succBlockShape m h).index 0 a.rev
    erw [TwoBlockJacquet.index_one, TwoBlockJacquet.index_zero]
    apply Fin.ext
    change t + 1 - (m 1 + 1 + a.val + 1) = m 0 + 1 - (a.val + 1)
    omega

private theorem blockWeyl_reverse_aux {n : ℕ} (B : BlockShape n)
    (hindex : ∀ (i : Fin B.length) (a : Fin (B.reverse.size i)),
      (B.reverse.index i a).rev = B.index i.rev a.rev) :
    B.leviEmbedding F.Carrier (fun i => weylLong (B.size i) F.Carrier) *
      B.reverseMatrix F.Carrier = weylLong n F.Carrier := by
  apply Units.ext
  ext r s
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective r
  obtain ⟨⟨j, b⟩, rfl⟩ := B.reverse.indexEquiv.surjective s
  obtain ⟨i, rfl⟩ := Fin.rev_surjective i
  change (B.leviEmbedding F.Carrier _ * B.reverseMatrix F.Carrier)
    (B.index i.rev a) (B.reverse.index j b) =
      weylLong n F.Carrier (B.index i.rev a) (B.reverse.index j b)
  erw [BlockShape.reverseMatrix, mul_permutation_entry, B.reversePermutation_index,
    weylLong_entry, hindex]
  by_cases hij : i = j
  · subst j
    erw [B.leviEmbedding_apply_same, weylLong_entry]
    by_cases hb : b.rev = a
    · exact (ite_eq_left hb).trans (ite_eq_left (congrArg (B.index i.rev) hb)).symm
    · exact (ite_eq_right hb).trans
        (ite_eq_right (fun e => hb ((B.index i.rev).injective e))).symm
  · erw [B.leviEmbedding_apply_ne F.Carrier _ a b
      (fun e => hij (Fin.rev_injective e))]
    have hne : B.index j.rev b.rev ≠ B.index i.rev a := by
      intro e
      have e' := congrArg Sigma.fst (B.indexEquiv.injective e)
      exact hij (Fin.rev_injective e').symm
    erw [ite_eq_right hne]

private theorem blockWeyl_reverse :
    (succBlockShape m h).leviEmbedding F.Carrier
        (fun i => weylLong (m i + 1) F.Carrier) *
      (succBlockShape m h).reverseMatrix F.Carrier = weylLong (t + 1) F.Carrier :=
  blockWeyl_reverse_aux F (succBlockShape m h) (reverse_index h)

private theorem blockWeyl_sq :
    (fun i : Fin 2 => weylLong (m i + 1) F.Carrier) *
      (fun i : Fin 2 => weylLong (m i + 1) F.Carrier) = 1 := by
  funext i
  exact weylLong_mul_self _ _

private theorem blockWeyl_modulus :
    F.canonicalTopologicalData.leviModulus (succBlockShape m h)
      (fun i => weylLong (m i + 1) F.Carrier) = 1 := by
  let q := F.canonicalTopologicalData.leviModulus (succBlockShape m h)
    (fun i => weylLong (m i + 1) F.Carrier)
  have hq : q * q = 1 := by
    rw [← map_mul, blockWeyl_sq F, map_one]
  apply Units.ext
  apply NNReal.eq
  have he : (q : ℝ) * (q : ℝ) = 1 := by
    simpa only [Units.val_mul, NNReal.coe_mul, Units.val_one, NNReal.coe_one] using
      congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hq
  have hp : 0 ≤ (q : ℝ) := (q : ℝ≥0).coe_nonneg
  change (q : ℝ) = 1
  nlinarith

private theorem blockWeyl_eval :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    ∀ (f : TwoBlockJacquet.Sections F h sigma) (g : GeneralLinear (t + 1) F.Carrier),
      TwoBlockJacquet.sectionEval F h sigma f
        ((succBlockShape m h).leviEmbedding F.Carrier
          (fun i => weylLong (m i + 1) F.Carrier) * g) =
        (succBlockShape m h).blockTensor sigma (fun i => weylLong (m i + 1) F.Carrier)
          (TwoBlockJacquet.sectionEval F h sigma f g) := by
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro f g
  have hc := F.canonicalTopologicalData.normalizedOppositeParabolicInduced_covariant
    (succBlockShape m h) ((succBlockShape m h).blockTensor sigma) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier
      (fun i => weylLong (m i + 1) F.Carrier)) g
  simpa only [BlockShape.oppositeLeviInParabolic_val,
    BlockShape.oppositeLeviProjection_section, blockWeyl_modulus F h,
    Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, one_smul] using hc

private theorem rawCarrierTransport :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    let mD := fun i : Fin 2 => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
    let WD := fun i : Fin 2 => W i.rev
    letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
    letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
    let sigmaD := fun i : Fin 2 => inverseTransposePullback (sigma i.rev)
    (∀ i, IsSmooth (sigma i)) →
    ∃ E : Representation.Equiv
        (inverseTransposePullback (TwoBlockJacquet.inducedRep F h sigma))
        (TwoBlockJacquet.inducedRep F hD sigmaD),
      ∀ f g, TwoBlockJacquet.sectionEval F hD sigmaD (E f) g =
        PiTensorProduct.reindex ℂ W Fin.revPerm
          (TwoBlockJacquet.sectionEval F h sigma f
            ((succBlockShape m h).reverseMatrix F.Carrier *
              inverseTranspose (t + 1) F.Carrier g)) := by
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  dsimp only
  intro hsigma
  let T := F.canonicalTopologicalData
  let B := succBlockShape m h
  letI : ∀ i : Fin B.reverse.length, AddCommGroup (W i.rev) := fun i => hadd i.rev
  letI : ∀ i : Fin B.reverse.length, Module ℂ (W i.rev) := fun i => hmod i.rev
  obtain ⟨C, hC, _⟩ := glOppositeProductReversal p F T (t + 1) B W sigma hsigma
  let D : Representation.Equiv
      ((T.normalizedOppositeParabolicInduced B (B.blockTensor sigma)).comp
        (inverseTranspose (t + 1) F.Carrier).toMonoidHom)
      ((T.normalizedProductInduced B.reverse (fun i => sigma i.rev)).comp
        (inverseTranspose (t + 1) F.Carrier).toMonoidHom) :=
    Representation.Equiv.mk C.toLinearEquiv (fun g => C.isIntertwining' _)
  let J := T.inverseTransposeProductToOppositeEquiv B.reverse (fun i => sigma i.rev)
  refine ⟨D.trans J, ?_⟩
  intro f g
  exact hC f (inverseTranspose (t + 1) F.Carrier g)

private theorem carrierTransport :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
    let mD := fun i : Fin 2 => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
    let WD := fun i : Fin 2 => W i.rev
    letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
    letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
    let sigmaD := fun i : Fin 2 => inverseTransposePullback (sigma i.rev)
    let B := succBlockShape m h
    let wB : B.Levi F.Carrier := fun i => weylLong (m i + 1) F.Carrier
    let R := PiTensorProduct.reindex ℂ W Fin.revPerm
    let T := fun g => weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g
    (∀ i, IsSmooth (sigma i)) →
    ∃ E : Representation.Equiv
        (inverseTransposePullback (TwoBlockJacquet.inducedRep F h sigma))
        (TwoBlockJacquet.inducedRep F hD sigmaD),
      (∀ f g, TwoBlockJacquet.sectionEval F hD sigmaD (E f) g =
        R ((B.blockTensor sigma wB) (TwoBlockJacquet.sectionEval F h sigma f (T g)))) ∧
      (∀ fD g, TwoBlockJacquet.sectionEval F h sigma (E.symm fD) g =
        (B.blockTensor sigma wB)
          (R.symm (TwoBlockJacquet.sectionEval F hD sigmaD fD (T g)))) := by
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  dsimp only
  intro hsigma
  obtain ⟨E, hE⟩ := rawCarrierTransport F h sigma hsigma
  let B := succBlockShape m h
  let wB : B.Levi F.Carrier := fun i => weylLong (m i + 1) F.Carrier
  let R := PiTensorProduct.reindex ℂ W Fin.revPerm
  let T := fun g => weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g
  have hA : ∀ v, B.blockTensor sigma wB (B.blockTensor sigma wB v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, blockWeyl_sq F, map_one, Module.End.one_apply]
  have hT : ∀ g, T (T g) = g := by
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    exact fun g => weylInverseTranspose_involutive (t + 1) F.Carrier g
  have hf : ∀ f g, TwoBlockJacquet.sectionEval F _ _ (E f) g =
      R (B.blockTensor sigma wB (TwoBlockJacquet.sectionEval F h sigma f (T g))) := by
    intro f g
    rw [hE]
    congr 1
    have hw : B.reverseMatrix F.Carrier * inverseTranspose (t + 1) F.Carrier g =
        B.leviEmbedding F.Carrier wB * T g := by
      dsimp [T]
      rw [← blockWeyl_reverse F h]
      dsimp only [B, wB]
      rw [← mul_assoc, ← mul_assoc, ← map_mul, blockWeyl_sq F, map_one, one_mul]
    rw [hw]
    exact blockWeyl_eval F h sigma f (T g)
  refine ⟨E, hf, ?_⟩
  intro fD g
  have hh := congrArg R.symm (hf (E.symm fD) (T g))
  rw [E.apply_symm_apply, hT, R.symm_apply_apply] at hh
  exact ((congrArg (B.blockTensor sigma wB) hh).trans (hA _)).symm

private theorem radicalConjugate
    (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
    let mD := fun i : Fin 2 => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
    weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier
        (TwoBlockJacquet.upperRadical hD F.Carrier X) * weylLong (t + 1) F.Carrier =
      TwoBlockJacquet.upperRadical h F.Carrier (fun i j => -X j.rev i.rev) := by
  dsimp only
  apply Units.ext
  ext r s
  obtain ⟨r, rfl⟩ := Fin.rev_surjective r
  obtain ⟨s, rfl⟩ := Fin.rev_surjective s
  let mD := fun i : Fin 2 => m i.rev
  let hD : ∑ i, (mD i + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  obtain ⟨⟨i, a⟩, rfl⟩ := (succBlockShape mD hD).indexEquiv.surjective r
  obtain ⟨⟨j, b⟩, rfl⟩ := (succBlockShape mD hD).indexEquiv.surjective s
  change (weylLong (t + 1) F.Carrier *
      inverseTranspose (t + 1) F.Carrier (TwoBlockJacquet.upperRadical hD F.Carrier X) *
      weylLong (t + 1) F.Carrier)
        ((succBlockShape mD hD).index i a).rev ((succBlockShape mD hD).index j b).rev = _
  erw [weylLong_conjugate_entry, Fin.rev_rev, Fin.rev_rev, inverseTranspose_entry,
    ← TwoBlockJacquet.upperRadical_neg, reverse_index h, reverse_index h]
  fin_cases i <;> fin_cases j
  · erw [TwoBlockJacquet.upperRadical_index_zero_zero,
      TwoBlockJacquet.upperRadical_index_one_one]
    change (if b = a then (1 : F.Carrier) else 0) =
      (if a.rev = b.rev then 1 else 0)
    simp only [Fin.rev_inj, eq_comm]
  · erw [TwoBlockJacquet.upperRadical_index_one_zero,
      TwoBlockJacquet.upperRadical_index_one_zero]
  · erw [TwoBlockJacquet.upperRadical_index_zero_one,
      TwoBlockJacquet.upperRadical_index_zero_one]
    change -X b a = -X b.rev.rev a.rev.rev
    rw [Fin.rev_rev, Fin.rev_rev]
  · erw [TwoBlockJacquet.upperRadical_index_one_one,
      TwoBlockJacquet.upperRadical_index_zero_zero]
    change (if b = a then (1 : F.Carrier) else 0) =
      (if a.rev = b.rev then 1 else 0)
    simp only [Fin.rev_inj, eq_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem tensorScalar :
    let mD := fun i : Fin 2 => m i.rev
    let hD : ∑ i, (mD i + 1) = t + 1 :=
      (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
    let WD := fun i : Fin 2 => W i.rev
    letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
    letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
    let sigmaD := fun i : Fin 2 => inverseTransposePullback (sigma i.rev)
    let B := succBlockShape m h
    let wB : B.Levi F.Carrier := fun i => weylLong (m i + 1) F.Carrier
    let R := PiTensorProduct.reindex ℂ W Fin.revPerm
    ∀ (ell : ∀ i, W i →ₗ[ℂ] ℂ) (z : (succBlockShape mD hD).Levi F.Carrier)
      (v : PiTensorProduct ℂ W),
      TwoBlockJacquet.tensorContraction
          (fun i => (ell i.rev).comp (sigma i.rev (weylLong (m i.rev + 1) F.Carrier)))
        ((succBlockShape mD hD).blockTensor sigmaD z (R (B.blockTensor sigma wB v))) =
      TwoBlockJacquet.tensorContraction ell
        (B.blockTensor sigma (fun i => wB i * inverseTranspose (m i + 1) F.Carrier
          (GeneralLinear.reindex
            (finCongr (congrArg (fun k => m k + 1) (Fin.rev_rev i))) (z i.rev)) * wB i) v) := by
  dsimp only
  intro ell z v
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [BlockShape.blockTensor, map_smul, FiniteTensor.external_tprod,
      PiTensorProduct.reindex_tprod, TwoBlockJacquet.tensorContraction_tprod,
      Fin.prod_univ_two]
    erw [FiniteTensor.external_tprod, TwoBlockJacquet.tensorContraction_tprod]
    simp only [Fin.prod_univ_two]
    change c •
      ((ell 1) (sigma 1 (weylLong (m 1 + 1) F.Carrier)
        (sigma 1 (inverseTranspose (m 1 + 1) F.Carrier (z 0))
          (sigma 1 (weylLong (m 1 + 1) F.Carrier) (v 1)))) *
      (ell 0) (sigma 0 (weylLong (m 0 + 1) F.Carrier)
        (sigma 0 (inverseTranspose (m 0 + 1) F.Carrier (z 1))
          (sigma 0 (weylLong (m 0 + 1) F.Carrier) (v 0))))) =
      c • ((ell 0) (sigma 0 (weylLong (m 0 + 1) F.Carrier *
          inverseTranspose (m 0 + 1) F.Carrier (z 1) * weylLong (m 0 + 1) F.Carrier)
        (v 0)) *
      (ell 1) (sigma 1 (weylLong (m 1 + 1) F.Carrier *
          inverseTranspose (m 1 + 1) F.Carrier (z 0) * weylLong (m 1 + 1) F.Carrier)
        (v 1)))
    simp only [map_mul, Module.End.mul_apply]
    rw [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

end Carrier


section Rectangular

variable {K : Type*} [AddCommGroup K] [TopologicalSpace K] [MeasurableSpace K]
  [MeasurableNeg K]

private theorem measurable_rho (a b : ℕ) :
    Measurable (fun (X : Matrix (Fin b) (Fin a) K) (i : Fin a) (j : Fin b) =>
      -X j.rev i.rev) :=
  Measurable.of_eval_matrix _ fun _ _ => Matrix.measurable_apply.neg

-- The rectangular-cylinder argument is adapted from the Library's elementary
-- measurePreserving_transpose_rectangularMeasure, without importing its analytic consumers.
private theorem measurePreserving_rho (nu : AdditiveHaarMeasure K)
    [SigmaFinite nu.measure] [Measure.IsNegInvariant nu.measure] (a b : ℕ) :
    MeasurePreserving
      (fun (X : Matrix (Fin b) (Fin a) K) (i : Fin a) (j : Fin b) => -X j.rev i.rev)
      (rectangularMeasure nu b a) (rectangularMeasure nu a b) := by
  refine ⟨measurable_rho a b, ?_⟩
  symm
  refine Measure.pi_eq_generateFrom
    (C := fun _ : Fin a => Set.pi Set.univ '' Set.pi Set.univ
      fun _ : Fin b => {s : Set K | MeasurableSet s})
    (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => nu.measure.toFiniteSpanningSetsIn) ?_
  intro S hS
  choose s hs hSs using hS
  obtain rfl : S = fun i => Set.pi Set.univ (s i) := funext fun i => (hSs i).symm
  have hmeas : MeasurableSet
      (Set.pi Set.univ (fun i => Set.pi Set.univ (s i)) : Set (Matrix (Fin a) (Fin b) K)) :=
    MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j => hs i j (Set.mem_univ j)
  have hmap := Measure.map_apply (μ := rectangularMeasure nu b a) (measurable_rho a b) hmeas
  have hpre : (fun (X : Matrix (Fin b) (Fin a) K) (i : Fin a) (j : Fin b) => -X j.rev i.rev) ⁻¹'
      (Set.pi Set.univ (fun i => Set.pi Set.univ (s i)) : Set (Matrix (Fin a) (Fin b) K)) =
      Set.pi Set.univ (fun j : Fin b => Set.pi Set.univ
        (fun i : Fin a => (fun x : K => -x) ⁻¹' s i.rev j.rev)) := by
    ext X
    constructor
    · intro h j _ i _
      simpa only [Set.mem_preimage, Fin.rev_rev] using h i.rev trivial j.rev trivial
    · intro h i _ j _
      simpa only [Set.mem_preimage, Fin.rev_rev] using h j.rev trivial i.rev trivial
  refine hmap.trans ?_
  rw [hpre]
  change Measure.pi (fun _ : Fin b => Measure.pi (fun _ : Fin a => nu.measure)) _ = _
  simp only [Measure.pi_pi]
  have hn : ∀ i j, nu.measure ((fun x : K => -x) ⁻¹' s i j) = nu.measure (s i j) :=
    fun i j => (Measure.measurePreserving_neg nu.measure).measure_preimage ((hs i j trivial).nullMeasurableSet)
  simp only [hn]
  calc
    (∏ j : Fin b, ∏ i : Fin a, nu.measure (s i.rev j.rev)) =
        ∏ j : Fin b, ∏ i : Fin a, nu.measure (s i j) := by
      rw [← Equiv.prod_comp Fin.revPerm (fun j : Fin b => ∏ i : Fin a, nu.measure (s i j))]
      apply Finset.prod_congr rfl
      intro j _
      exact Equiv.prod_comp Fin.revPerm (fun i : Fin a => nu.measure (s i j.rev))
    _ = _ := Finset.prod_comm

end Rectangular

end TwoBlockDualSectionJacquet

set_option backward.isDefEq.respectTransparency false in
/-- Actual reversed-dual section transport with the supplied product Haar measures. -/
theorem twoBlockDualSectionJacquet.{uF, uW} :
    TwoBlockDualSectionJacquetStatement.{uF, uW} := by
  unfold TwoBlockDualSectionJacquetStatement
  intro p hp F
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  letI : BorelSpace F.Carrier := ⟨rfl⟩
  letI := F.canonicalTopologicalData.sigmaCompactSpace
  letI : MeasurableNeg F.Carrier := ⟨continuous_neg.measurable⟩
  intro t m h
  letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (t + 1)
  intro W hadd hmod sigma hsigma
  dsimp only
  let mD : Fin 2 → ℕ := fun i => m i.rev
  let hD : ∑ i, (mD i + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  let WD : Fin 2 → Type uW := fun i => W i.rev
  letI : ∀ i, AddCommGroup (WD i) := fun i => hadd i.rev
  letI : ∀ i, Module ℂ (WD i) := fun i => hmod i.rev
  let sigmaD := fun i : Fin 2 => inverseTransposePullback (sigma i.rev)
  let B := succBlockShape m h
  let wB : B.Levi F.Carrier := fun i => weylLong (m i + 1) F.Carrier
  let T := fun g => weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g
  let rho : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ≃
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier :=
    { toFun := fun X i j => -X j.rev i.rev
      invFun := fun Y i j => -Y j.rev i.rev
      left_inv := by intro X; ext i j; simp
      right_inv := by intro Y; ext i j; simp }
  obtain ⟨E, hE, hEsymm⟩ := TwoBlockDualSectionJacquet.carrierTransport F h sigma hsigma
  refine ⟨E, hE, hEsymm, ?_⟩
  intro psi ell
  let psiD := psi.scale (-1)
  let ellD : ∀ i, glInverseFunctionals psiD (mD i) (sigmaD i) :=
    fun i => secondDualFunctional psi (sigma i.rev) (ell i.rev)
  have hscalar (f : TwoBlockJacquet.Sections F h sigma)
      (g : GeneralLinear (t + 1) F.Carrier) (z : (succBlockShape mD hD).Levi F.Carrier) :
      TwoBlockJacquet.scalarSection (fun i => (ellD i).val) (E f) g z =
        TwoBlockJacquet.scalarSection (fun i => (ell i).val) f (T g)
          (fun i => wB i * inverseTranspose (m i + 1) F.Carrier
            (GeneralLinear.reindex
              (finCongr (congrArg (fun k => m k + 1) (Fin.rev_rev i)))
              (z i.rev)) * wB i) := by
    erw [TwoBlockJacquet.scalarSection_def, TwoBlockJacquet.scalarSection_def, hE]
    exact TwoBlockDualSectionJacquet.tensorScalar F h sigma (fun i => (ell i).val) z _
  have hone (f : TwoBlockJacquet.Sections F h sigma)
      (g : GeneralLinear (t + 1) F.Carrier) :
      TwoBlockJacquet.scalarSection (fun i => (ellD i).val) (E f) g 1 =
        TwoBlockJacquet.scalarSection (fun i => (ell i).val) f (T g) 1 := by
    rw [hscalar]
    congr 1
    funext i
    simp only [Pi.one_apply, map_one, mul_one, wB, weylLong_mul_self]
  refine ⟨hscalar, hone, ?_⟩
  intro nu
  let mu := rectangularMeasure nu (m 0 + 1) (m 1 + 1)
  let muD := rectangularMeasure nu (m 1 + 1) (m 0 + 1)
  have hrho : MeasurePreserving rho muD mu :=
    TwoBlockDualSectionJacquet.measurePreserving_rho nu _ _
  have hrhoi : MeasurePreserving rho.symm mu muD :=
    TwoBlockDualSectionJacquet.measurePreserving_rho nu _ _
  let erho : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ≃ᵐ
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier :=
    { toEquiv := rho
      measurable_toFun := TwoBlockDualSectionJacquet.measurable_rho _ _
      measurable_invFun := TwoBlockDualSectionJacquet.measurable_rho _ _ }
  have hrad (g : GeneralLinear (t + 1) F.Carrier)
      (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
      T (TwoBlockJacquet.upperRadical hD F.Carrier X * g) =
        TwoBlockJacquet.upperRadical h F.Carrier (rho X) * T g := by
    dsimp only [T]
    rw [map_mul]
    calc
      _ = (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier
          (TwoBlockJacquet.upperRadical hD F.Carrier X) * weylLong (t + 1) F.Carrier) *
          (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier g) := by
        rw [mul_assoc (weylLong (t + 1) F.Carrier * inverseTranspose (t + 1) F.Carrier
          (TwoBlockJacquet.upperRadical hD F.Carrier X)),
          ← mul_assoc (weylLong (t + 1) F.Carrier) (weylLong (t + 1) F.Carrier),
          weylLong_mul_self, one_mul, mul_assoc]
      _ = _ := by
        rw [TwoBlockDualSectionJacquet.radicalConjugate F h]
        rfl
  have hkernel (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
      TwoBlockJacquet.positiveKernel (m := mD) psiD X =
        TwoBlockJacquet.positiveKernel (m := m) psi (rho X) := by
    rw [TwoBlockJacquet.positiveKernel_apply, TwoBlockJacquet.positiveKernel_apply]
    change psi.complex ((-1 : F.Carrier) * X (Fin.last (m 1)) 0) =
      psi.complex (-X (0 : Fin (m 1 + 1)).rev (Fin.last (m 0)).rev)
    simp only [neg_one_mul, Fin.rev_zero, Fin.rev_last]
  have hraw (f : TwoBlockJacquet.Sections F h sigma)
      (g : GeneralLinear (t + 1) F.Carrier)
      (X : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
      TwoBlockJacquet.integrand psiD (fun i => (ellD i).val) (E f) g X =
        TwoBlockJacquet.integrand psi (fun i => (ell i).val) f (T g) (rho X) := by
    erw [TwoBlockJacquet.integrand_def, TwoBlockJacquet.integrand_def,
      hone, hrad, hkernel]
  have hat (f : TwoBlockJacquet.Sections F h sigma)
      (g : GeneralLinear (t + 1) F.Carrier) :
      TwoBlockJacquet.IsAbsIntegrableAt psiD (fun i => (ellD i).val) muD (E f) g ↔
        TwoBlockJacquet.IsAbsIntegrableAt psi (fun i => (ell i).val) mu f (T g) := by
    unfold TwoBlockJacquet.IsAbsIntegrableAt
    have heq : TwoBlockJacquet.integrand psiD (fun i => (ellD i).val) (E f) g =
        TwoBlockJacquet.integrand psi (fun i => (ell i).val) f (T g) ∘ rho :=
      funext (hraw f g)
    rw [heq]
    exact hrho.integrable_comp_emb erho.measurableEmbedding
  refine ⟨hrho, hrhoi, hraw, hat, ?_, ?_⟩
  · intro f
    constructor
    · intro hf g
      have hh := (hat f (T g)).mp (hf (T g))
      have hT : T (T g) = g := weylInverseTranspose_involutive (t + 1) F.Carrier g
      rw [hT] at hh
      exact hh
    · intro hf g
      exact (hat f g).mpr (hf (T g))
  · intro f g
    change (∫ X, TwoBlockJacquet.integrand psiD (fun i => (ellD i).val) (E f) g X ∂muD) =
      ∫ Y, TwoBlockJacquet.integrand psi (fun i => (ell i).val) f (T g) Y ∂mu
    simp only [hraw]
    exact hrho.integral_comp erho.measurableEmbedding _

end Langlands.RankinSelberg
