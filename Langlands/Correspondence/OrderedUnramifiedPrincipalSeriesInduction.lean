import Langlands.Correspondence.SphericalStandardLPrerequisites
import Langlands.Representation.RankinSelberg.TemperedLFactorDual
import Langlands.Representation.RankinSelberg.InducedTailLFactorProof
import Langlands.Representation.RankinSelberg.AdjacentRankUpperFamilyTransport
import Langlands.Representation.RankinSelberg.FiniteLFactorMultiplicativity
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Correspondence.OrderedUnramifiedPrincipalSeries

open RankinSelberg HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance canonicalTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance canonicalValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance canonicalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance canonicalGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The rank-one block of an unramified character. -/
abbrev block (z : ℂˣ) : Representation ℂ (GeneralLinear 1 F.Carrier) ℂ :=
  characterRepresentation (determinantQuasiCharacter F 1 (Unramified.character F z))

/-- The trivial rank-one representation. -/
abbrev trivialBlock : Representation ℂ (GeneralLinear 1 F.Carrier) ℂ :=
  characterRepresentation (determinantQuasiCharacter F 1 1)

theorem block_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier) (z : ℂˣ) :
    IsOfWhittakerType 0 (standardCharacter ψ 0) (block F z) :=
  rankOneCharacter_isOfWhittakerType p F ψ (Unramified.character F z)

theorem trivialBlock_isOfWhittakerType
    (ψ : UnitaryAdditiveCharacter F.Carrier) :
    IsOfWhittakerType 0 (standardCharacter ψ 0) (trivialBlock F) :=
  rankOneCharacter_isOfWhittakerType p F ψ 1

theorem borel_sum (r : ℕ) : ∑ _i : Fin (r + 1), ((fun _ => 0 : Fin (r + 1) → ℕ) _i + 1) = r + 1 := by
  simp

/-- The ordered principal series is literally the canonical normalized
induction of its rank-one blocks along the upper-Borel shape. -/
example (r : ℕ) (z : Fin (r + 1) → ℂˣ) :
    Unramified.principalSeriesOfTuple F z =
      F.canonicalNormalizedProductInduced (succBlockShape (fun _ => 0) (borel_sum r))
        (fun i => block F (z i)) := rfl

theorem symmetricLPolynomial_rankCast
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier)
    {r r' n : ℕ} (h : r = r') {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) W) (P : ℂ[X]) :
    IsPadicSymmetricLPolynomial F ψ μ
        (rankCastRepresentation (congrArg (· + 1) h) π) σ P ↔
      IsPadicSymmetricLPolynomial F ψ μ π σ P := by
  subst h
  rfl

private abbrev pairIndices (b : ℕ) : Fin 2 → ℕ := ![0, b]

private theorem pairSum (b : ℕ) :
    ∑ i, (pairIndices b i + 1) = (0 + 1 + b) + 1 := by
  simp only [pairIndices, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

private def successorPairFamily
    {b : ℕ} {V₁ V₂ : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (0 + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear (b + 1) F.Carrier) V₂)
    (i : Fin 2) :
    Representation ℂ (GeneralLinear (pairIndices b i + 1) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i) :=
  match i with
  | 0 => π₁
  | 1 => π₂

/-- The successor-indexed pair family and the literal two-block family define
equivalent actual inductions (a copy of the private Library construction in
`InducedTailConditionalAssemblyProof`, specialized to a rank-one first block). -/
private def successorPairInducedEquiv
    {b : ℕ} {V₁ V₂ : Type u}
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (π₁ : Representation ℂ (GeneralLinear (0 + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (GeneralLinear (b + 1) F.Carrier) V₂) :
    Representation.Equiv
      (F.canonicalNormalizedProductInduced
        (succBlockShape (pairIndices b) (pairSum b)) (successorPairFamily F π₁ π₂))
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (0 + 1) (b + 1) (Nat.succ_pos 0) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂)) := by
  let D := Σ s : {s : Fin 2 → ℕ //
      (∀ i, 0 < s i) ∧ ∑ i, s i = (0 + 1 + b) + 1},
    ∀ i, Representation ℂ (GeneralLinear (s.val i) F.Carrier)
      (Shahidi.pairCarrier V₁ V₂ i)
  let d₀ : D := ⟨⟨fun i => pairIndices b i + 1,
    ⟨fun i => Nat.succ_pos _, pairSum b⟩⟩, successorPairFamily F π₁ π₂⟩
  let d₁ : D := ⟨⟨![0 + 1, b + 1],
    ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
      by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        omega⟩⟩,
    Shahidi.pairFamily π₁ π₂⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let predicate : D → Prop := fun d =>
    Nonempty (Representation.Equiv
      (F.canonicalNormalizedProductInduced
        ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
      (F.canonicalNormalizedProductInduced
        (Shahidi.twoBlocks (0 + 1) (b + 1) (Nat.succ_pos 0) (Nat.succ_pos b))
        (Shahidi.pairFamily π₁ π₂)))
  have h : predicate d₀ := by
    rw [hd]
    exact ⟨Representation.Equiv.refl _⟩
  exact Classical.choice h

/-- The `ULift` conjugation of the published tail lemma is equivalent to the
original representation. -/
def uliftConjEquiv.{w, uG, uV} {G : Type uG} [Group G] {V : Type uV}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    ρ.Equiv (((ULift.moduleEquiv (R := ℂ) (M := V)).symm.conjRingEquiv.toMonoidHom).comp ρ :
      Representation ℂ G (ULift.{w} V)) :=
  Representation.Equiv.mk ULift.moduleEquiv.symm (by intro g; rfl)

/-- The upper-Borel shape of a tuple of length `b + 2`. -/
private abbrev borelShape (b : ℕ) : BlockShape (b + 1 + 1) :=
  succBlockShape (fun _ : Fin (b + 2) => 0) (borel_sum (b + 1))

/-- Tail divisibility for the ordered principal series, from
`inducedTailLFactor`: the tail tuple against trivial `GL₁` has a certified
L-polynomial dividing the certified L-polynomial of the full tuple. -/
theorem exists_tail_dvd
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (b : ℕ) (z : Fin (b + 2) → ℂˣ) {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (Unramified.principalSeriesOfTuple F z) (trivialBlock F) P) :
    ∃ Ptail : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val
      (Unramified.principalSeriesOfTuple F (Fin.tail z)) (trivialBlock F) Ptail ∧
      Ptail ∣ P := by
  let T := F.canonicalTopologicalData
  let B := borelShape b
  let bundled : ∀ i, SmoothRep ℂ (GeneralLinear (B.size i) F.Carrier) := fun i =>
    SmoothRep.of (block F (z i)) (block_isOfWhittakerType F ψ (z i)).1.1
  let z₀ := z (B.headIndex rfl)
  let zt : Fin (b + 1) → ℂˣ := fun j => z (B.tailIndex rfl j)
  have hzt : zt = Fin.tail z := by
    funext j
    rfl
  let π₂ := Unramified.principalSeriesOfTuple F zt
  have hπ₂ : IsOfWhittakerType b (standardCharacter ψ b) π₂ :=
    normalizedProductWhittakerType p F ψ b (b + 1) (fun _ => 0) (borel_sum b)
      (fun j => block F (zt j)) (fun j => block_isOfWhittakerType F ψ (zt j))
  obtain ⟨Pfull, Ptail', hfull, htail, hdiv⟩ :=
    inducedTailLFactor p F ψ ν 0 b 0 (block F z₀) π₂ (trivialBlock F)
      (block_isOfWhittakerType F ψ z₀) hπ₂ (trivialBlock_isOfWhittakerType F ψ)
  refine ⟨Ptail', hzt ▸ htail, ?_⟩
  suffices hPfull : Pfull = P by
    rw [← hPfull]
    exact hdiv
  refine hfull.unique ?_
  let π₁' : Representation ℂ (GeneralLinear (0 + 1) F.Carrier) (ULift.{uF} ℂ) :=
    ((ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm.conjRingEquiv.toMonoidHom).comp
      (block F z₀)
  let π₂' : Representation ℂ (GeneralLinear (b + 1) F.Carrier) (ULift.{0} _) :=
    ((ULift.moduleEquiv (R := ℂ)).symm.conjRingEquiv.toMonoidHom).comp π₂
  let σ := fun i => (T.headTailProductFactors B rfl bundled i).representation
  let τ := successorPairFamily F π₁' π₂'
  have hsize : ∀ i : Fin 2, (B.headTailShape rfl).size i = pairIndices b i + 1 := by
    intro i
    fin_cases i
    · rfl
    · show ∑ _j : Fin (b + 1), (0 + 1) = b + 1
      simp
  have hr : 0 + 1 + b = b + 1 := by omega
  have hsum : ∑ i, (pairIndices b i + 1) = b + 1 + 1 := (pairSum b).trans (by omega)
  have e : ∀ i : Fin 2, (rankCastRepresentation (hsize i) (σ i)).Equiv (τ i) := by
    intro i
    match i with
    | 0 =>
      exact (universeLiftEquiv.{uF} (block F z₀)).symm.trans
        (uliftConjEquiv.{uF} (block F z₀))
    | 1 =>
      exact (normalizedProductRankCastEquiv T (B.tailShape rfl) (hsize 1)
        (fun j => block F (zt j))).trans (uliftConjEquiv.{0} π₂)
  let E₂ := Padic.normalizedProductInducedEquiv_of_sizes F (B.headTailShape rfl)
    (pairIndices b) hsize hsum σ τ e
  have h₁ := (IsPadicSymmetricLPolynomial.congr_equiv
    ((T.headTailProductInductionEquiv B rfl bundled).trans E₂)
    (Representation.Equiv.refl (trivialBlock F))).mp hP
  have h₂ := (IsPadicSymmetricLPolynomial.congr_equiv
    (normalizedProductRankCastEquiv T (succBlockShape (pairIndices b) (pairSum b))
      (congrArg (· + 1) hr) τ).symm
    (Representation.Equiv.refl (trivialBlock F))).mp h₁
  have h₃ := (symmetricLPolynomial_rankCast F ψ ν.val hr _ _ P).mp h₂
  exact (IsPadicSymmetricLPolynomial.congr_equiv (successorPairInducedEquiv F π₁' π₂')
    (Representation.Equiv.refl (trivialBlock F))).mp h₃

/-- Pulling an unramified rank-one block back along inverse transpose inverts
its Satake parameter. -/
theorem inverseTransposePullback_block (z : ℂˣ) :
    inverseTransposePullback (block F z) = block F z⁻¹ := by
  ext g : 1
  refine LinearMap.ext fun v => ?_
  change ((Unramified.character F z (determinant (inverseTranspose (0 + 1) F.Carrier g)) : ℂˣ) :
      ℂ) • v = ((Unramified.character F z⁻¹ (determinant g) : ℂˣ) : ℂ) • v
  rw [RankOneGammaTwist.determinant_inverseTranspose, map_inv, Unramified.character_apply,
    Unramified.character_apply, inv_zpow]

/-- Inverse transpose fixes the trivial rank-one representation. -/
theorem inverseTransposePullback_trivialBlock :
    inverseTransposePullback (trivialBlock F) = trivialBlock F := by
  ext g : 1
  refine LinearMap.ext fun v => ?_
  rfl

/-- The rank-one input: for every unitary additive character and Haar measure,
the certified L-polynomial of an unramified rank-one block against trivial
`GL₁` is `1 - z X`. -/
def RankOneLPolynomialInput : Prop :=
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := borel F.Carrier; AdditiveHaarMeasure F.Carrier) (z : ℂˣ) (P : ℂ[X]),
    IsPadicSymmetricLPolynomial F ψ μ (block F z) (trivialBlock F) P →
      P = 1 - C (z : ℂ) * X

private theorem eval_one_sub_ne_zero {w x : ℂ} (h : ‖w‖ * ‖x‖ < 1) :
    (1 - C w * X).eval x ≠ 0 := by
  rw [eval_sub, eval_one, eval_mul, eval_C, eval_X, sub_ne_zero]
  intro hx
  have : ‖w * x‖ = 1 := by rw [← hx, norm_one]
  rw [norm_mul] at this
  linarith

/-- The reflection step: once the L-polynomial of the tail parameters divides
the certified polynomial, the residual is removed by reflection rigidity with
root-exclusion radii `‖z₀‖⁻¹` and `‖z₀‖`. -/
theorem eq_prod_of_tail_dvd (hone : RankOneLPolynomialInput F)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (b : ℕ) (z : Fin (b + 1) → ℂˣ) (hz : Monotone (fun i => ‖(z i : ℂ)‖)) {P : ℂ[X]}
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val
      (Unramified.principalSeriesOfTuple F z) (trivialBlock F) P)
    (hdiv : (∏ i : Fin b, (1 - C (z i.succ : ℂ) * X)) ∣ P) :
    P = ∏ i, (1 - C (z i : ℂ) * X) := by
  classical
  have hn : ∑ _j : Fin 1, ((fun _ : Fin 1 => 0) _j + 1) = 0 + 1 := by simp
  have hπ : ∀ i, IsOfWhittakerType ((fun _ : Fin (b + 1) => 0) i)
      (standardCharacter ψ ((fun _ : Fin (b + 1) => 0) i)) (block F (z i)) :=
    fun i => block_isOfWhittakerType F ψ (z i)
  have hσ : ∀ j, IsOfWhittakerType ((fun _ : Fin 1 => 0) j)
      (standardCharacter ψ ((fun _ : Fin 1 => 0) j)) (trivialBlock F) :=
    fun _ => trivialBlock_isOfWhittakerType F ψ
  let d := TemperedLFactorDivisibility.twoFamilyLPolynomialData F ψ ν
    (fun _ : Fin (b + 1) => 0) (fun _ : Fin 1 => 0) (borel_sum b) hn
    (fun i => block F (z i)) (fun _ => trivialBlock F) hπ hσ
  obtain ⟨e⟩ := TemperedLFactorDual.nonempty_dualTwoFamilyLPolynomialData F ψ ν
    (fun _ : Fin (b + 1) => 0) (fun _ : Fin 1 => 0) (borel_sum b) hn
    (fun i => block F (z i)) (fun _ => trivialBlock F) hπ hσ
  obtain ⟨g⟩ := TemperedLFactorGamma.nonempty_reflectedRatioData F ψ ν
    (fun _ : Fin (b + 1) => 0) (fun _ : Fin 1 => 0) (borel_sum b) hn
    (fun i => block F (z i)) (fun _ => trivialBlock F) hπ hσ
    d.inducedPolynomial e.inducedPolynomial d.blockPolynomial e.blockPolynomial
    d.induced_spec d.block_spec e.induced_spec e.block_spec
  have hσs : ∀ j : Fin 1, IsSmooth ((fun _ => trivialBlock F) j) :=
    fun _ => (trivialBlock_isOfWhittakerType F ψ).1.1
  have hPd : P = d.inducedPolynomial :=
    hP.unique ((singleBlock_L_iff F (fun _ : Fin 1 => 0) (fun _ => trivialBlock F) _ hn
      hσs).mp d.induced_spec)
  have hQ : ∀ i j, d.blockPolynomial i j = 1 - C (z i : ℂ) * X :=
    fun i j => hone ψ ν.val (z i) _ (d.block_spec i j)
  have hQD : ∀ i j, e.blockPolynomial i j = 1 - C (((z i)⁻¹ : ℂˣ) : ℂ) * X := by
    intro i j
    have h : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback (block F (z i)))
        (inverseTransposePullback (trivialBlock F)) (e.blockPolynomial i j) :=
      e.block_spec i j
    rw [inverseTransposePullback_block, inverseTransposePullback_trivialBlock] at h
    exact hone (ψ.scale (-1)) ν.val (z i)⁻¹ _ h
  have hB : ∏ i, ∏ j, d.blockPolynomial i j = ∏ i, (1 - C (z i : ℂ) * X) :=
    Finset.prod_congr rfl fun i _ => by rw [Fin.prod_univ_one, hQ]
  have hBD : ∏ i, ∏ j, e.blockPolynomial i j =
      ∏ i, (1 - C (((z i)⁻¹ : ℂˣ) : ℂ) * X) :=
    Finset.prod_congr rfl fun i _ => by rw [Fin.prod_univ_one, hQD]
  have hPne : d.inducedPolynomial ≠ 0 := by
    intro hzero
    have hc := d.induced_spec.coeff_zero
    simp only [hzero, coeff_zero, zero_ne_one] at hc
  have hPDne : e.inducedPolynomial ≠ 0 := by
    intro hzero
    have hc := e.induced_spec.coeff_zero
    simp only [hzero, coeff_zero, zero_ne_one] at hc
  have hz0 : 0 < ‖(z 0 : ℂ)‖ := norm_pos_iff.mpr (z 0).ne_zero
  -- the dual product has no roots in the disk of radius `‖z₀‖`
  have hBDpole : ∀ x : ℂ, ‖x‖ < ‖(z 0 : ℂ)‖ →
      (∏ i, ∏ j, e.blockPolynomial i j).eval x ≠ 0 := by
    intro x hx
    rw [hBD, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => eval_one_sub_ne_zero ?_
    have hzi : ‖(z 0 : ℂ)‖ ≤ ‖(z i : ℂ)‖ := hz (Fin.zero_le i)
    have hzi0 : 0 < ‖(z i : ℂ)‖ := lt_of_lt_of_le hz0 hzi
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_mul_lt_iff₀ hzi0, mul_one]
    exact lt_of_lt_of_le hx hzi
  have hBDne : (∏ i, ∏ j, e.blockPolynomial i j) ≠ 0 := by
    intro hzero
    exact hBDpole 0 (by simp [hz0]) (by rw [hzero, eval_zero])
  have hidentity := TemperedLFactorAlgebra.reflected_identity_of_quotient_ratio
    (LocalFactor.residueReflection F) g.coefficient g.exponent hPne hPDne hBDne
    d.quotient.factorization e.quotient.factorization g.ratio
  have hfac : ∏ i, (1 - C (z i : ℂ) * X) = d.quotient.polynomial * P := by
    rw [← hB, hPd]
    exact d.quotient.factorization
  -- the residual divides `1 - z₀ X`
  obtain ⟨S, hS⟩ := hdiv
  have hT : (∏ i : Fin b, (1 - C (z i.succ : ℂ) * X)) ≠ 0 := by
    intro hzero
    have h0 := congrArg (eval 0) hzero
    simp [eval_prod] at h0
  have hDS : 1 - C (z 0 : ℂ) * X = d.quotient.polynomial * S := by
    have hfac' := hfac
    rw [hS, Fin.prod_univ_succ] at hfac'
    apply mul_right_cancel₀ hT
    calc
      _ = _ := hfac'
      _ = _ := by ring
  have hDpole : ∀ x : ℂ, ‖x‖ < ‖(z 0 : ℂ)‖⁻¹ → d.quotient.polynomial.eval x ≠ 0 := by
    intro x hx hzero
    have hne := eval_one_sub_ne_zero (w := (z 0 : ℂ)) (x := x)
      (by rwa [← lt_inv_mul_iff₀ hz0, mul_one])
    rw [hDS, eval_mul, hzero, zero_mul] at hne
    exact hne rfl
  have hEpole : ∀ x : ℂ, ‖x‖ < ‖(z 0 : ℂ)‖ → e.quotient.polynomial.eval x ≠ 0 := by
    intro x hx hzero
    apply hBDpole x hx
    rw [e.quotient.factorization, eval_mul, hzero, zero_mul]
  obtain ⟨hDone, -⟩ := reflectionRigidity ‖(z 0 : ℂ)‖⁻¹ ‖(z 0 : ℂ)‖
    (LocalFactor.residueReflection F) g.coefficient g.exponent
    d.quotient.polynomial e.quotient.polynomial (inv_pos.mpr hz0) hz0
    (by rw [inv_mul_cancel₀ hz0.ne']; exact TemperedLFactorAlgebra.norm_residueReflection_lt_one F)
    d.quotient.coeff_zero e.quotient.coeff_zero hDpole hEpole hidentity
  rw [hDone, one_mul] at hfac
  exact hfac.symm

/-- Induction on the length of the tuple: the certified L-polynomial of an
ordered unramified principal series against trivial `GL₁` is the Euler product,
given the rank-one input. -/
theorem eq_prod_of_certificate (hone : RankOneLPolynomialInput F)
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) :
    ∀ (b : ℕ) (z : Fin (b + 1) → ℂˣ), Monotone (fun i => ‖(z i : ℂ)‖) → ∀ {P : ℂ[X]},
      IsPadicSymmetricLPolynomial F ψ ν.val
        (Unramified.principalSeriesOfTuple F z) (trivialBlock F) P →
      P = ∏ i, (1 - C (z i : ℂ) * X)
  | 0, z, hz, _, hP => eq_prod_of_tail_dvd F hone ψ ν 0 z hz hP (by simp)
  | b + 1, z, hz, P, hP => by
    obtain ⟨Pt, hPt, hdvd⟩ := exists_tail_dvd F ψ ν b z hP
    have htail := eq_prod_of_certificate hone ψ ν b (Fin.tail z)
      (fun i j hij => hz (Fin.succ_le_succ_iff.mpr hij)) hPt
    refine eq_prod_of_tail_dvd F hone ψ ν (b + 1) z hz hP ?_
    rw [htail] at hdvd
    exact hdvd

/-- The target statement follows from the rank-one input. -/
theorem orderedUnramifiedPrincipalSeriesLPolynomial_of_rankOne
    (hone : RankOneLPolynomialInput F) :
    OrderedUnramifiedPrincipalSeriesLPolynomialStatement.{uF} F := by
  intro ψ ν hν r z P hz hP
  rw [Unramified.Eigenvalues.eulerPolynomial_ofTuple]
  exact eq_prod_of_certificate F hone ψ ⟨ν, hν⟩ r z hz hP

end Langlands.Correspondence.OrderedUnramifiedPrincipalSeries
