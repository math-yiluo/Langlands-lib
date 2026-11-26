import Langlands.AllField.Representation.RankinSelberg.TemperedTypePremisesStatement
import Langlands.AllField.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistLFactorProof
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.Representation.Induction.HeterogeneousPairs

/-!
# Certified L-polynomials for standard modules of tempered-type data

Over a nonarchimedean local field `F`: the L-polynomial relation of pairs of arbitrary
positive ranks; Whittaker type of standard modules; the certified polynomials of two
standard modules and of their blocks, with the normalized residual of JPSS 1983,
Theorem (3.1)(ii); the pole bound of the twisted blocks from (8.4); and the tail
divisibility of standard modules from (9.3).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg

open Langlands.RankinSelberg (IsOfWhittakerType succBlockShape)
open _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

section Rank

variable {ψ : UnitaryAdditiveCharacter F} {ν : letI := borel F; AdditiveHaarMeasure F}

/-- `L(s, π × σ) = 1 / P(q^(-s))` for representations of arbitrary ranks: the relation
`IsPadicSymmetricLPolynomial` when both ranks are positive, and `False` otherwise. -/
def IsPadicRankLPolynomial (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F; AdditiveHaarMeasure F)
    {n t : ℕ} {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F) V)
    (σ : Representation ℂ (GeneralLinear t F) W) (P : ℂ[X]) : Prop :=
  match n, t, π, σ with
  | _ + 1, _ + 1, π, σ => IsPadicSymmetricLPolynomial F ψ ν π σ P
  | _, _, _, _ => False

theorem isPadicRankLPolynomial_succ {r k : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (GeneralLinear (k + 1) F) W} {P : ℂ[X]} :
    IsPadicRankLPolynomial ψ ν π σ P ↔ IsPadicSymmetricLPolynomial F ψ ν π σ P :=
  Iff.rfl

theorem IsPadicRankLPolynomial.unique {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear t F) W} {P P' : ℂ[X]}
    (h : IsPadicRankLPolynomial ψ ν π σ P) (h' : IsPadicRankLPolynomial ψ ν π σ P') :
    P = P' := by
  match n, t, π, σ, h, h' with
  | _ + 1, _ + 1, _, _, h, h' => exact IsPadicSymmetricLPolynomial.unique h h'

theorem IsPadicRankLPolynomial.coeff_zero {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear t F) W} {P : ℂ[X]}
    (h : IsPadicRankLPolynomial ψ ν π σ P) : P.coeff 0 = 1 := by
  match n, t, π, σ, h with
  | _ + 1, _ + 1, _, _, h => exact IsPadicSymmetricLPolynomial.coeff_zero h

theorem IsPadicRankLPolynomial.ne_zero {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear t F) W} {P : ℂ[X]}
    (h : IsPadicRankLPolynomial ψ ν π σ P) : P ≠ 0 := by
  intro hz
  have := h.coeff_zero
  simp [hz] at this

theorem isPadicRankLPolynomial_comm {n t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F) V)
    (σ : Representation ℂ (GeneralLinear t F) W) (P : ℂ[X]) :
    IsPadicRankLPolynomial ψ ν π σ P ↔ IsPadicRankLPolynomial ψ ν σ π P := by
  cases n with
  | zero => cases t <;> exact Iff.rfl
  | succ n =>
    cases t with
    | zero => exact Iff.rfl
    | succ t => exact TemperedLFactorDivisibility.symmetricLPolynomial_swap F ψ ν π σ P

theorem IsPadicRankLPolynomial.congr_equiv {n t : ℕ} {V : Type uV} {W : Type uW}
    {V₂ : Type*} {W₂ : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
    {π : Representation ℂ (GeneralLinear n F) V}
    {σ : Representation ℂ (GeneralLinear t F) W}
    {π₂ : Representation ℂ (GeneralLinear n F) V₂}
    {σ₂ : Representation ℂ (GeneralLinear t F) W₂}
    (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) {P : ℂ[X]} :
    IsPadicRankLPolynomial ψ ν π σ P ↔ IsPadicRankLPolynomial ψ ν π₂ σ₂ P := by
  match n, t, π, σ, π₂, σ₂, φ, φ' with
  | _ + 1, _ + 1, _, _, _, _, φ, φ' => exact IsPadicSymmetricLPolynomial.congr_equiv φ φ'
  | 0, _, _, _, _, _, _, _ => exact Iff.rfl
  | _ + 1, 0, _, _, _, _, _, _ => exact Iff.rfl

end Rank

namespace TemperedTypeDatum

/-- The standard module of a datum of positive rank is of Whittaker type. -/
theorem standardModule_whittaker (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (d : TemperedTypeDatum.{uF, uV} (F := F) (r + 1)) :
    IsOfWhittakerType r (standardCharacter ψ r) d.standardModule := by
  rcases d with ⟨⟨k, size, pos, total⟩, τ, hi, ht, hw, u, hu⟩
  obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
    ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
  exact normalizedProductWhittakerType F ψ r k m total _
    (fun i => (isOfRankWhittakerType_twist_iff ψ _ (u i)).mpr (hw ψ i))

/-- Whittaker type of the standard module at its actual positive rank. -/
theorem standardModule_rankWhittaker (ψ : UnitaryAdditiveCharacter F) {n : ℕ} (hn : 0 < n)
    (d : TemperedTypeDatum.{uF, uV} (F := F) n) :
    IsOfRankWhittakerType ψ d.standardModule := by
  cases n with
  | zero => omega
  | succ r => exact d.standardModule_whittaker ψ

end TemperedTypeDatum

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)

/-- Certified polynomials of two standard modules and of their pairs of twisted blocks,
with a normalized residual `D` such that `∏ i, ∏ j, Q i j = D * P`. -/
structure TemperedTypeLPolynomialData {n t : ℕ}
    (d : TemperedTypeDatum.{uF, uV} (F := F) n) (e : TemperedTypeDatum.{uF, uW} (F := F) t) where
  inducedPolynomial : ℂ[X]
  blockPolynomial : Fin d.shape.length → Fin e.shape.length → ℂ[X]
  induced_spec : IsPadicRankLPolynomial ψ ν.val d.standardModule e.standardModule
    inducedPolynomial
  block_spec : ∀ i j, IsPadicRankLPolynomial ψ ν.val
    (d.twistedBlock i).representation (e.twistedBlock j).representation (blockPolynomial i j)
  quotient : Langlands.RankinSelberg.TemperedLFactorAlgebra.NormalizedPolynomialQuotient
    inducedPolynomial (∏ i, ∏ j, blockPolynomial i j)

/-- JPSS 1983, Theorem (3.1)(ii), in both families: the certified polynomials and the
normalized residual for two data of positive rank. -/
def temperedTypeLPolynomialData {r t : ℕ}
    (d : TemperedTypeDatum.{uF, uV} (F := F) (r + 1))
    (e : TemperedTypeDatum.{uF, uW} (F := F) (t + 1)) :
    TemperedTypeLPolynomialData ψ ν d e :=
  Classical.choice <| by
    rcases d with ⟨⟨k, size, pos, total⟩, τ, hiτ, htτ, hwτ, u, hu⟩
    rcases e with ⟨⟨l, size', pos', total'⟩, σ, hiσ, htσ, hwσ, v, hv⟩
    obtain ⟨m, rfl⟩ : ∃ m : Fin k → ℕ, size = fun i => m i + 1 :=
      ⟨fun i => size i - 1, funext fun i => (Nat.sub_add_cancel (pos i)).symm⟩
    obtain ⟨n, rfl⟩ : ∃ n : Fin l → ℕ, size' = fun j => n j + 1 :=
      ⟨fun j => size' j - 1, funext fun j => (Nat.sub_add_cancel (pos' j)).symm⟩
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
    let c := TemperedLFactorDivisibility.twoFamilyLPolynomialData F ψ ν m n total total'
      π σ' hπ hσ
    exact ⟨{
      inducedPolynomial := c.inducedPolynomial
      blockPolynomial := c.blockPolynomial
      induced_spec := c.induced_spec
      block_spec := c.block_spec
      quotient := c.quotient }⟩

section Tail

variable {ψ ν}

set_option maxHeartbeats 800000 in
/-- Tail divisibility for an arbitrary two-block shape, from JPSS (9.3) in the form
`InducedTailLFactorAt`. -/
theorem twoBlockShapeTailLPolynomial_dvd
    (htail : InducedTailLFactorAt.{uF, uV, uV, uW} F) {n t : ℕ}
    (B : BlockShape n) (hB : B.length = 2)
    {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (π : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (t + 1) F) W)
    (hπ : ∀ i, IsOfRankWhittakerType ψ (π i))
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ)
    {P Ptail : ℂ[X]}
    (hP : IsPadicRankLPolynomial ψ ν.val
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced B π) σ P)
    (htail' : IsPadicRankLPolynomial ψ ν.val (π (Fin.cast hB.symm (1 : Fin 2))) σ Ptail) :
    Ptail ∣ P := by
  rcases B with ⟨k, size, pos, total⟩
  dsimp at hB
  subst k
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, size = ![a + 1, b + 1] := by
    refine ⟨size 0 - 1, size 1 - 1, ?_⟩
    funext i
    fin_cases i <;> simp [Nat.sub_add_cancel (pos _)]
  have htotal : (a + 1) + (b + 1) = n := by simpa using total
  subst n
  obtain ⟨Pfull, Qtail, hfull, hQtail, hdiv⟩ :=
    htail ψ ν a b t (π 0) (π 1) σ (hπ 0) (hπ 1) hσ
  let e := (⟨⟩ : LocalFieldData F).normalizedProductInducedEquiv
    (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
    (σ := Shahidi.pairFamily
      ((ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp (π 0) :
        Representation ℂ (GeneralLinear (a + 1) F) (ULift.{uV} (V 0)))
      ((ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp (π 1) :
        Representation ℂ (GeneralLinear (b + 1) F) (ULift.{uV} (V 1))))
    (τ := π)
    (Fin.cases (literalULiftEquiv (π 0)).symm
      (Fin.cases (literalULiftEquiv (π 1)).symm (fun i => i.elim0)))
  have hfull' := (IsPadicSymmetricLPolynomial.congr_equiv e
    (Representation.Equiv.refl σ)).mp hfull
  have heq : P = Pfull := hP.unique hfull'
  have hteq : Ptail = Qtail := htail'.unique hQtail
  simpa only [heq, hteq] using hdiv

set_option maxHeartbeats 800000 in
/-- Tail divisibility for standard modules: the certified polynomial of the tail
standard module against a test representation of Whittaker type divides that of the
standard module. -/
theorem TemperedTypeDatum.standardTailLPolynomial_dvd
    (htail : InducedTailLFactorAt.{uF, max uF uV, max uF uV, uW} F) {n t k : ℕ}
    (d : TemperedTypeDatum.{uF, uV} (F := F) n) (h : d.shape.length = k + 2)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear t F) W) (hσ : IsOfRankWhittakerType ψ σ)
    {P Ptail : ℂ[X]}
    (hP : IsPadicRankLPolynomial ψ ν.val d.standardModule σ P)
    (htail' : IsPadicRankLPolynomial ψ ν.val (d.tail h).standardModule σ Ptail) :
    Ptail ∣ P := by
  cases t with
  | zero => exact hσ.elim
  | succ t =>
    have hf : ∀ i, IsOfRankWhittakerType ψ (d.headTailStandardFactors h i).representation := by
      intro i
      fin_cases i
      · exact (d.twistedBlock_whittaker ψ (d.shape.headIndex h)).of_equiv
          (universeLiftEquiv.{uF} (d.twistedBlock (d.shape.headIndex h)).representation)
      · exact (d.tail h).standardModule_rankWhittaker ψ (d.shape.tailRank_pos h)
    exact twoBlockShapeTailLPolynomial_dvd htail (d.shape.headTailShape h) rfl
      (fun i => (d.headTailStandardFactors h i).representation) σ hf hσ
      ((IsPadicRankLPolynomial.congr_equiv (d.headTailStandardModuleEquiv h)
        (Representation.Equiv.refl σ)).mp hP) htail'

end Tail

section Twist

variable {ψ ν}

/-- Real determinant twists of both members rescale the L-polynomial:
`L(s, ν^a π × ν^b σ) = L(s + a + b, π × σ)`. -/
theorem realPowerTwistLPolynomial {r t : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear (r + 1) F) V}
    {σ : Representation ℂ (GeneralLinear (t + 1) F) W} {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π σ P) (a b : ℝ) :
    IsPadicSymmetricLPolynomial F ψ ν.val
      (realPowerTwist ((⟨⟩ : LocalFieldData F).determinantNorm (r + 1)) a π)
      (realPowerTwist ((⟨⟩ : LocalFieldData F).determinantNorm (t + 1)) b σ)
      ((P.comp (C (((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-(a : ℂ))) * X)).comp
        (C (((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-(b : ℂ))) * X)) := by
  let T : LocalFieldData F := ⟨⟩
  have hχ (c : ℝ) (x : Fˣ) :
      (realPowerCharacter T.normalizedAbsUnits c x : ℂ) =
        ((T.normalizedAbs (x : F) : ℝ) : ℂ) ^ (c : ℂ) := by
    exact Complex.ofReal_cpow (T.normalizedAbs_nonneg _) c
  have hs := (unramifiedTwistLFactor F ψ ν r t π σ
    (a : ℂ) (realPowerCharacter T.normalizedAbsUnits a) (hχ a) P hP).2
  exact (unramifiedTwistLFactor F ψ ν r t
    (realPowerTwist (T.determinantNorm (r + 1)) a π) σ
    (b : ℂ) (realPowerCharacter T.normalizedAbsUnits b) (hχ b) _ hs).1

/-- The pole bound for real twists of irreducible tempered representations, from the
untwisted bound (8.4): a certified polynomial of `(ν^a τ, ν^b σ)` has no zero in the disk
of radius `q^(a + b)`. -/
theorem realPowerTwistRankLPolynomial_poleFree
    (hpole : TemperedPoleBoundStatement.{uF, uV, uW} F) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (GeneralLinear n F) V) (σ : Representation ℂ (GeneralLinear m F) W)
    (hiτ : Representation.IsIrreducible τ) (htτ : IsTemperedRepresentation τ)
    (hiσ : Representation.IsIrreducible σ) (htσ : IsTemperedRepresentation σ)
    (a b : ℝ) {Q : ℂ[X]}
    (hQ : IsPadicRankLPolynomial ψ ν.val
      (realPowerTwist ((⟨⟩ : LocalFieldData F).determinantNorm n) a τ)
      (realPowerTwist ((⟨⟩ : LocalFieldData F).determinantNorm m) b σ) Q) :
    ∀ w : ℂ, ‖w‖ < ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (a + b) →
      Q.eval w ≠ 0 := by
  cases n with
  | zero => omega
  | succ r =>
  cases m with
  | zero => omega
  | succ t =>
  intro w hw
  let T : LocalFieldData F := ⟨⟩
  let q : ℝ := T.residueCardinality
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  have hQ' := realPowerTwistLPolynomial (isPadicRankLPolynomial_succ.mp hQ) (-a) (-b)
  rw [realPowerTwist_neg_cancel, realPowerTwist_neg_cancel] at hQ'
  have hne := hpole ψ ν r t τ σ hiτ htτ hiσ htσ _ hQ'
    ((T.residueCardinality : ℂ) ^ (-(a : ℂ)) * ((T.residueCardinality : ℂ) ^ (-(b : ℂ)) * w))
  have hn (c : ℝ) : ‖(T.residueCardinality : ℂ) ^ (-(c : ℂ))‖ = q ^ (-c) := by
    rw [← Complex.ofReal_neg, Complex.norm_cpow_real, Complex.norm_natCast]
  have hsmall : ‖(T.residueCardinality : ℂ) ^ (-(a : ℂ)) *
      ((T.residueCardinality : ℂ) ^ (-(b : ℂ)) * w)‖ < 1 := by
    rw [norm_mul, norm_mul, hn, hn, ← mul_assoc,
      ← Real.rpow_add hq, ← neg_add, Real.rpow_neg hq.le]
    exact (inv_mul_lt_one₀ (Real.rpow_pos_of_pos hq (a + b))).mpr hw
  have hval : ((Q.comp (C ((T.residueCardinality : ℂ) ^ (-((-a : ℝ) : ℂ))) * X)).comp
      (C ((T.residueCardinality : ℂ) ^ (-((-b : ℝ) : ℂ))) * X)).eval
        ((T.residueCardinality : ℂ) ^ (-(a : ℂ)) *
          ((T.residueCardinality : ℂ) ^ (-(b : ℂ)) * w)) = Q.eval w := by
    have hq0 : (T.residueCardinality : ℂ) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
    simp only [eval_comp, eval_mul, eval_C, eval_X, Complex.ofReal_neg, neg_neg]
    congr 1
    have hA (c : ℝ) : (T.residueCardinality : ℂ) ^ (c : ℂ) ≠ 0 :=
      fun h => hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rw [Complex.cpow_neg, Complex.cpow_neg]
    field_simp
    exact mul_div_cancel_left₀ w (mul_ne_zero (hA a) (hA b))
  exact hval ▸ hne hsmall

end Twist

end Langlands.AllField.RankinSelberg
