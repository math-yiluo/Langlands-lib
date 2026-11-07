import Langlands.Correspondence.BaseLocalEuler
import Langlands.Correspondence.SegmentEpsilonAlgebra
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.LanglandsFactors
import Langlands.LocalFactor.ResidueReflection

/-!
# The block-pair gamma law as a local rational-function identity

Let `T = (B ⊗ Sp(a + 1)) ⊗ (B' ⊗ Sp(b + 1))` be the local tensor of two
uncentered blocks and `L_k = ω^k B ⊗ B'` with zero monodromy. Restricting to the
bottom intermediate field, the block-pair gamma law (Henniart 2002, §2.4) at
the regular real points gives, with `c X^d` the quotient correction of the
bottom-field tensor of blocks,
`c X^d · LR(T) = ∏_i ∏_j LR(L_(i+j))` as rational functions, where `LR` is the
reflected L-ratio at the local inertia and the published geometric Frobenius.
The epsilon value of the bottom-field tensor of blocks is the product of the
epsilon values of the pairs `(ω^(i+j) ρ, ρ')` times `c q^(-ds)`.
-/

noncomputable section

universe uF uP

open Polynomial

namespace Langlands.Correspondence

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
  LocalFactor.CommonClosureGamma LocalFactor.PairBlock

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The local tensor of the uncentered blocks `B ⊗ Sp(a + 1)` and `B' ⊗ Sp(b + 1)`. -/
abbrev localBlockTensor (B B' : LocalWeilRepresentation.{uF, uP} F) (a b : ℕ) :
    LocalWeilDeligneRepresentation.{uF, uP} F :=
  WeilDeligneRepresentation.tensor
    (WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom B (a + 1))
    (WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom B' (b + 1))

/-- The local tensor `ω^k B ⊗ B'` of zero-monodromy pairs. -/
abbrev localTwistTensor (B B' : LocalWeilRepresentation.{uF, uP} F) (k : ℕ) :
    LocalWeilDeligneRepresentation.{uF, uP} F :=
  WeilDeligneRepresentation.tensor
    (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom
      (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ k) B))
    (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B')

/-- The bottom-field tensor of the blocks of the lifted restrictions. -/
abbrev baseBlockTensor (B B' : LocalWeilRepresentation.{uF, uP} F) (a b : ℕ) :
    Pair.{uF, uP} F (baseExtension F) :=
  WeilDeligneRepresentation.tensor
    (WeilDeligneRepresentation.block (normCharacter F (baseExtension F)).toMonoidHom
      (baseLift F B) (a + 1))
    (WeilDeligneRepresentation.block (normCharacter F (baseExtension F)).toMonoidHom
      (baseLift F B') (b + 1))

/-- The restriction of the local tensor of blocks is the bottom-field tensor of blocks. -/
def restrictBlockTensorBaseEquiv (B B' : LocalWeilRepresentation.{uF, uP} F) (a b : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (localBlockTensor F B B' a b))
      (baseBlockTensor F B B' a b) :=
  (WeilDeligneRepresentation.restrictTensorEquiv _ _ _).trans
    (WeilDeligneRepresentation.tensorCongr (restrictBlockBaseEquiv F B (a + 1))
      (restrictBlockBaseEquiv F B' (b + 1)))

/-- The bottom-field spectral variable is the local one. -/
theorem baseSpectralParameter_eq (s : ℂ) :
    (spectralParameter (residueCardinality F (baseExtension F))
        (residueCardinality_pos F (baseExtension F)) s : ℂ) =
      RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s := by
  rw [spectralParameter_eq_cpow, baseResidueCardinality_real]
  simp [RankinSelberg.spectralPoint]

/-- The bottom-field spectral variable at `1 - s` is `δ / q^(-s)`. -/
theorem baseSpectralParameter_one_sub (s : ℂ) :
    (spectralParameter (residueCardinality F (baseExtension F))
        (residueCardinality_pos F (baseExtension F)) (1 - s) : ℂ) =
      (residueReflection F : ℂ) /
        RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality s := by
  rw [WeilDeligne.spectralParameter_one_sub, Units.val_div_eq_div_val,
    WeilDeligne.coe_reflectionScale, baseSpectralParameter_eq, baseResidueCardinality_real,
    coe_residueReflection]
  push_cast
  rfl

private theorem ne_zero_of_coeff_zero {P : ℂ[X]} (h : P.coeff 0 = 1) : P ≠ 0 := by
  rintro rfl
  simp at h

open RankinSelberg.RationalEvaluation in
private theorem regularAt_C_mul_X_pow (c : ℂ) (d : ℕ) {x : ℂ} {R : RatFunc ℂ}
    (hR : RegularAt R x) : RegularAt (RatFunc.C c * RatFunc.X ^ d * R) x := by
  have hc : RegularAt (RatFunc.C c) x := by
    simpa using RegularAt.polynomial (z := x) (Polynomial.C c)
  have hX : RegularAt (RatFunc.X : RatFunc ℂ) x := by
    simpa using RegularAt.polynomial (z := x) (Polynomial.X : ℂ[X])
  exact (hc.mul (hX.pow d)).mul hR

open RankinSelberg.RationalEvaluation in
private theorem eval_C_mul_X_pow (c : ℂ) (d : ℕ) {x : ℂ} {R : RatFunc ℂ}
    (hR : RegularAt R x) :
    RatFunc.eval (RingHom.id ℂ) x (RatFunc.C c * RatFunc.X ^ d * R) =
      c * x ^ d * RatFunc.eval (RingHom.id ℂ) x R := by
  have hc : RegularAt (RatFunc.C c) x := by
    simpa using RegularAt.polynomial (z := x) (Polynomial.C c)
  have hX : RegularAt (RatFunc.X : RatFunc ℂ) x := by
    simpa using RegularAt.polynomial (z := x) (Polynomial.X : ℂ[X])
  rw [eval_mul (hc.mul (hX.pow d)) hR, eval_mul hc (hX.pow d), eval_pow hX d, RatFunc.eval_C,
    RatFunc.eval_X]
  rfl

open RankinSelberg.RationalEvaluation in
/-- **Henniart 2.4 as a rational identity.** For continuous `B`, `B'` and any
geometric Frobenius `Φ` over the bottom field, with `c X^d` the quotient
correction of the bottom-field tensor of blocks at `Φ`,
`c X^d · LR(T) = ∏_i ∏_j LR(ω^(i+j) B ⊗ B')`, all reflected L-ratios taken at the
local inertia and the published geometric Frobenius. -/
theorem rationalLRatio_localBlockTensor (hBPG : BlockPairGamma.{uF, uP} F)
    (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uP} F)
    (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (B B' : LocalWeilRepresentation.{uF, uP} F) (hB : B.IsContinuous) (hB' : B'.IsContinuous)
    (a b : ℕ) (Φ : GeometricFrobenius F (baseExtension F)) :
    RatFunc.C (WeilDeligne.quotientConstantCorrection (baseBlockTensor F B B' a b)
          (inertia F (baseExtension F)) Φ.val : ℂ) *
        RatFunc.X ^ WeilDeligne.conductorCorrection (baseBlockTensor F B B' a b)
          (inertia F (baseExtension F)) *
        WeilDeligne.rationalLRatio (localBlockTensor F B B' a b) (localInertia F)
          (localGeometricFrobenius F) (residueReflection F) =
      ∏ i : Fin (a + 1), ∏ j : Fin (b + 1),
        WeilDeligne.rationalLRatio (localTwistTensor F B B' (i.val + j.val)) (localInertia F)
          (localGeometricFrobenius F) (residueReflection F) := by
  have hq : 1 < F.canonicalTopologicalData.residueCardinality :=
    F.canonicalTopologicalData.residueCardinality_gt_one
  have hρ := baseLift_isContinuous F hB
  have hρ' := baseLift_isContinuous F hB'
  -- the bottom-field Euler polynomials are the local ones
  have hT := eulerPolynomial_base_of_equiv F _ _ (restrictBlockTensorBaseEquiv F B B' a b) Φ
  have hT' := eulerPolynomial_dual_base_of_equiv F _ _ (restrictBlockTensorBaseEquiv F B B' a b) Φ
  have hK := fun (i : Fin (a + 1)) (j : Fin (b + 1)) =>
    eulerPolynomial_base_of_equiv F _ _ (restrictTwistedPairBaseEquiv F B B' (i.val + j.val)) Φ
  have hK' := fun (i : Fin (a + 1)) (j : Fin (b + 1)) =>
    eulerPolynomial_dual_base_of_equiv F _ _
      (restrictTwistedPairBaseEquiv F B B' (i.val + j.val)) Φ
  set δ := residueReflection F with hδdef
  set P := WeilDeligne.eulerPolynomial (localBlockTensor F B B' a b) (localInertia F)
    (localGeometricFrobenius F) with hPdef
  set P' := WeilDeligne.eulerPolynomial
    (WeilDeligneRepresentation.dual (localBlockTensor F B B' a b)) (localInertia F)
    (localGeometricFrobenius F) with hP'def
  set Q : Fin (a + 1) → Fin (b + 1) → ℂ[X] := fun i j =>
    WeilDeligne.eulerPolynomial (localTwistTensor F B B' (i.val + j.val)) (localInertia F)
      (localGeometricFrobenius F) with hQdef
  set Q' : Fin (a + 1) → Fin (b + 1) → ℂ[X] := fun i j =>
    WeilDeligne.eulerPolynomial
      (WeilDeligneRepresentation.dual (localTwistTensor F B B' (i.val + j.val)))
      (localInertia F) (localGeometricFrobenius F) with hQ'def
  -- the finite exceptional set
  set N : ℂ[X] := P * ∏ i, ∏ j, Q i j
  set N' : ℂ[X] := P' * ∏ i, ∏ j, Q' i j
  have hN : N ≠ 0 := mul_ne_zero (ne_zero_of_coeff_zero (WeilDeligne.eulerPolynomial_coeff_zero _ _ _))
    (Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
      ne_zero_of_coeff_zero (WeilDeligne.eulerPolynomial_coeff_zero _ _ _))
  have hN' : N' ≠ 0 := mul_ne_zero
    (ne_zero_of_coeff_zero (WeilDeligne.eulerPolynomial_coeff_zero _ _ _))
    (Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ =>
      ne_zero_of_coeff_zero (WeilDeligne.eulerPolynomial_coeff_zero _ _ _))
  set Z : Set ℂ := {x | IsRoot N x} ∪ (fun y => (δ : ℂ) / y) '' {y | IsRoot N' y}
  have hZ : Z.Finite :=
    (finite_setOfPred_isRoot hN).union ((finite_setOfPred_isRoot hN').image _)
  set U : Set ℂ := ((fun s : ℝ => RankinSelberg.spectralPoint
    F.canonicalTopologicalData.residueCardinality (s : ℂ)) '' Set.Ioi 0) \ Z
  have hU : U.Infinite := (RankinSelberg.infinite_spectralPoints_on_right hq 0).sdiff hZ
  -- regularity at points of `U`
  have hreg : ∀ x ∈ U, ∃ s : ℝ, RankinSelberg.spectralPoint
      F.canonicalTopologicalData.residueCardinality (s : ℂ) = x ∧ x ≠ 0 ∧
      P.eval x ≠ 0 ∧ P'.eval ((δ : ℂ) / x) ≠ 0 ∧
      (∀ i j, (Q i j).eval x ≠ 0) ∧ (∀ i j, (Q' i j).eval ((δ : ℂ) / x) ≠ 0) := by
    rintro x ⟨⟨s, -, rfl⟩, hxZ⟩
    have hx0 : RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality
        (s : ℂ) ≠ 0 := RankinSelberg.spectralPoint_ne_zero_of_pos (by omega) _
    have h1 : N.eval (RankinSelberg.spectralPoint F.canonicalTopologicalData.residueCardinality
        (s : ℂ)) ≠ 0 := fun h => hxZ (Or.inl h)
    have h2 : N'.eval ((δ : ℂ) / RankinSelberg.spectralPoint
        F.canonicalTopologicalData.residueCardinality (s : ℂ)) ≠ 0 := fun h =>
      hxZ (Or.inr ⟨_, h, div_div_cancel₀ δ.ne_zero⟩)
    simp only [N, N', Polynomial.eval_mul, Polynomial.eval_prod, mul_ne_zero_iff,
      Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] at h1 h2
    exact ⟨s, rfl, hx0, h1.1, h2.1, fun i j => h1.2 i j, fun i j => h2.2 i j⟩
  have hRHS : ∀ x ∈ U, RegularAt (∏ i : Fin (a + 1), ∏ j : Fin (b + 1),
      WeilDeligne.rationalLRatio (localTwistTensor F B B' (i.val + j.val)) (localInertia F)
        (localGeometricFrobenius F) δ) x := by
    intro x hx
    obtain ⟨s, -, hx0, -, -, -, hQ'x⟩ := hreg x hx
    exact RegularAt.prod _ fun i _ => RegularAt.prod _ fun j _ =>
      regularAt_rationalLRatio _ _ _ δ hx0 (hQ'x i j)
  apply RankinSelberg.rationalFunction_eq_of_infinite_eval_eq _ _ U hU
  · intro x hx
    obtain ⟨s, -, hx0, -, hP'x, -, -⟩ := hreg x hx
    exact regularAt_C_mul_X_pow _ _ (regularAt_rationalLRatio _ _ _ δ hx0 hP'x)
  · exact hRHS
  · intro x hx
    have hRx := hRHS x hx
    obtain ⟨s, rfl, hx0, hPx, hP'x, hQx, hQ'x⟩ := hreg x hx
    -- the block-pair gamma law at the regular point `s`
    let sT : RegularPoint F (baseExtension F) (baseBlockTensor F B B' a b) Φ := ⟨(s : ℂ), by
      rw [hT, baseSpectralParameter_eq]; exact hPx, by
      rw [hT', baseSpectralParameter_one_sub]; exact hP'x⟩
    let t : (i : Fin (a + 1)) → (j : Fin (b + 1)) → RegularPoint F (baseExtension F)
        (twistedFactor F (baseExtension F)
          (FiniteRepresentation.tensor (baseLift F B) (baseLift F B')) (i.val + j.val)) Φ :=
      fun i j => ⟨(s : ℂ), by
        rw [hK, baseSpectralParameter_eq]; exact hQx i j, by
        rw [hK', baseSpectralParameter_one_sub]; exact hQ'x i j⟩
    have h := congrArg Units.val (quotientValue_mul_lRatioValue_block F hBPG eC ε hε
      (baseExtension F) ψ' μ (baseLift F B) (baseLift F B') hρ hρ' a b Φ sT t (fun _ _ => rfl))
    simp only [Units.val_mul, Units.coe_prod, quotientValue_eq_monomial, Units.val_pow_eq_pow_val,
      lRatioValue_eq] at h
    simp only [sT, t, hT, hT', hK, hK', baseSpectralParameter_one_sub] at h
    simp only [baseSpectralParameter_eq] at h
    rw [eval_C_mul_X_pow _ _ (regularAt_rationalLRatio _ _ _ δ hx0 hP'x),
      eval_rationalLRatio _ _ _ δ hx0 hP'x,
      eval_prod _ fun i _ => RegularAt.prod _ fun j _ =>
        regularAt_rationalLRatio _ _ _ δ hx0 (hQ'x i j)]
    refine h.trans (Finset.prod_congr rfl fun i _ => ?_)
    rw [eval_prod _ fun j _ => regularAt_rationalLRatio _ _ _ δ hx0 (hQ'x i j)]
    exact Finset.prod_congr rfl fun j _ => (eval_rationalLRatio _ _ _ δ hx0 (hQ'x i j)).symm

/-- The epsilon value of the bottom-field tensor of blocks: if the epsilon value of
each pair `(ω^(i+j) ρ, ρ')` of twisted factors is `c_ij q^(-m_ij s)`, then that of
the tensor of blocks is `(∏ c_ij · c) q^(-(Σ m_ij + d) s)`, with `c X^d` the
quotient correction at `Φ`. -/
theorem conditionalPairEpsilonValue_baseBlock (eC : ReciprocityFamily F)
    (ε : NonabelianSystem.Assignment.{uF, uP} F) (hε : NonabelianSystem.IsSystem F eC ε)
    (ψ' : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (B B' : LocalWeilRepresentation.{uF, uP} F) (hB : B.IsContinuous) (hB' : B'.IsContinuous)
    (a b : ℕ) (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ)
    (e : Fin (a + 1) → Fin (b + 1) → ℂˣ × ℤ)
    (he : ∀ i j, (conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
        (twistedFactor F (baseExtension F) (baseLift F B) (i.val + j.val))
        (twistedFactor F (baseExtension F) (baseLift F B') 0)
        (twistedFactor_isContinuous F _ _ (baseLift_isContinuous F hB) _)
        (twistedFactor_isContinuous F _ _ (baseLift_isContinuous F hB') 0) Φ s : ℂ) =
      RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (e i j).1 (e i j).2 s) :
    (conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
        (WeilDeligneRepresentation.block (normCharacter F (baseExtension F)).toMonoidHom
          (baseLift F B) (a + 1))
        (WeilDeligneRepresentation.block (normCharacter F (baseExtension F)).toMonoidHom
          (baseLift F B') (b + 1))
        (block_isContinuous F _ _ (baseLift_isContinuous F hB) (a + 1))
        (block_isContinuous F _ _ (baseLift_isContinuous F hB') (b + 1)) Φ s : ℂ) =
      RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality
        ((RankinSelberg.epsilonFactorProduct e).1 *
          WeilDeligne.quotientConstantCorrection (baseBlockTensor F B B' a b)
            (inertia F (baseExtension F)) Φ.val)
        ((RankinSelberg.epsilonFactorProduct e).2 +
          WeilDeligne.conductorCorrection (baseBlockTensor F B B' a b)
            (inertia F (baseExtension F))) s := by
  have hq : 1 < F.canonicalTopologicalData.residueCardinality :=
    F.canonicalTopologicalData.residueCardinality_gt_one
  have hρ := baseLift_isContinuous F hB
  have hρ' := baseLift_isContinuous F hB'
  have hij : ∀ (i : Fin (a + 1)) (j : Fin (b + 1)),
      (conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ' μ
        (twistedFactor F (baseExtension F) (baseLift F B) i)
        (twistedFactor F (baseExtension F) (baseLift F B') j)
        (twistedFactor_isContinuous F _ _ hρ i) (twistedFactor_isContinuous F _ _ hρ' j)
        Φ s : ℂ) =
      RankinSelberg.epsilonMonomial F.canonicalTopologicalData.residueCardinality
        (e i j).1 (e i j).2 s := fun i j => by
    rw [← he i j, conditionalPairEpsilonValue_twistedFactor F eC ε hε _ ψ' μ _ _ hρ hρ' i j Φ s,
      conditionalPairEpsilonValue_twistedFactor F eC ε hε _ ψ' μ _ _ hρ hρ' (i.val + j.val) 0 Φ s]
    rfl
  rw [conditionalPairEpsilonValue_block F eC ε hε _ ψ' μ _ _ hρ hρ' a b Φ s, Units.val_mul,
    quotientValue_eq_monomial, Units.val_mul, Units.val_pow_eq_pow_val, baseSpectralParameter_eq]
  simp only [Units.coe_prod, hij]
  rw [← RankinSelberg.epsilonMonomial_factorProduct e hq s]
  unfold RankinSelberg.epsilonMonomial
  push_cast
  rw [zpow_add₀ (RankinSelberg.spectralPoint_ne_zero_of_pos (by omega) s), zpow_natCast]
  ring

end Langlands.Correspondence
