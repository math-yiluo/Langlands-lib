import Langlands.BaseChange.CuspidalSelfPairDescentProfile
import Langlands.BaseChange.SigmaOrbitConjugates
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.BaseChange.SupercuspidalNormTwistedPairPolynomial
import Langlands.Group.GL.RankReindex
import Langlands.LocalField.PadicBridge
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.RankinSelberg.DiscreteSelfPairSupercuspidality
import Langlands.Representation.RankinSelberg.NormalizedProductSelfPairPolynomial
import Langlands.Representation.RankinSelberg.UnitaryCuspidalProductSelfPair

/-! # Identifying the discrete σ-orbit block with the local self-pair identity -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis RankinSelberg _root_.Polynomial

universe u v uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier]

local notation "T" => F.canonicalTopologicalData
local notation "U" => E.canonicalTopologicalData

open scoped PadicField.CanonicalLocalField

private local instance orbitGroup (K : PadicField p) (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n K.Carrier) :=
  K.canonicalTopologicalData.generalLinearTopologicalGroup n

private theorem normCharacter_isOpen_ker [FiniteDimensional F.Carrier E.Carrier]
    {κ : F.Carrierˣ →* ℂˣ} (hκ : IsNormTrivial E.Carrier κ) :
    IsOpen (κ.ker : Set F.Carrierˣ) := by
  let : NontriviallyNormedField F.Carrier := F.canonicalNormedField
  let : CompleteSpace F.Carrier := inferInstance
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact hκ.isOpen_ker

set_option maxHeartbeats 800000 in
private def lowerDenominator [FiniteDimensional F.Carrier E.Carrier]
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : LocalFactor.PadicAbelian.SelfDualHaar T ψ)
    {n : ℕ} (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hi : π.IsIrreducible) (hsc : IsSupercuspidal π) (hsq : (T).IsSquareIntegrable π)
    {κ : F.Carrierˣ →* ℂˣ} (hκ : IsNormTrivial E.Carrier κ) :
    {Q : ℂ[X] // IsPadicRankLPolynomial F ψ ν.val π
      (twist (κ.comp determinant) (smoothContragredient π)) Q ∧
      Q.eval ((T).residueCardinality : ℂ) ≠ 0} := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ r => exact normTwistedSupercuspidalSelfPairPolynomial F E.Carrier ψ ν π hi hsc hsq hκ

set_option maxHeartbeats 3000000 in
/-- For a given discrete σ-orbit decomposition, the certified self-pair
comparison implies supercuspidality of the block and the prescribed period. -/
theorem padicSigmaLiftOrbitIdentification_of_selfPair [FiniteDimensional F.Carrier E.Carrier]
    [IsModuleTopology F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (ψF : UnitaryAdditiveCharacter F.Carrier) (νF : LocalFactor.PadicAbelian.SelfDualHaar T ψF)
    (ψE : UnitaryAdditiveCharacter E.Carrier) (νE : LocalFactor.PadicAbelian.SelfDualHaar U ψE)
    {f n t m : ℕ} (hf : 0 < f) (hq : (U).residueCardinality = (T).residueCardinality ^ f)
    (hn : 0 < n) (hm : 0 < m) (hrank : t * m = n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hπi : π.IsIrreducible) (hπs : IsSupercuspidal π) (hπq : (T).IsSquareIntegrable π)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear n E.Carrier) W)
    {Y : Type uW} [AddCommGroup Y] [Module ℂ Y]
    (P₁ : Representation ℂ (GeneralLinear m E.Carrier) Y)
    (hP₁i : P₁.IsIrreducible) (hP₁q : (U).IsSquareIntegrable P₁)
    (hperiod : ∀ i : ℕ,
      Nonempty (P₁.Equiv (P₁.comp (entrywiseAut (σ ^ i) m).toMonoidHom)) ↔ t ∣ i)
    (horbit : Nonempty (P.Equiv ((sigmaOrbitProduct σ t hm P₁).comp
      (GeneralLinear.reindex (R := E.Carrier) (finCongr hrank)).symm.toMonoidHom)))
    (S : Finset (F.Carrierˣ →* ℂˣ)) (hS : ∀ κ, κ ∈ S ↔ IsNormTrivial E.Carrier κ)
    (hCompare : ∀ (B : ℂ[X]) (L : S → ℂ[X]),
      IsPadicRankLPolynomial E ψE νE.val P (smoothContragredient P) B →
      (∀ κ : S, IsPadicRankLPolynomial F ψF νF.val π
        (twist (κ.val.comp determinant) (smoothContragredient π)) (L κ)) →
      B.comp (X ^ f) = ∏ κ, L κ) :
    IsSupercuspidal P₁ ∧ t = Nat.card (normTwistStabilizer E.Carrier π) := by
  classical
  subst n
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have ht : 0 < t := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hn
  let B := BlockShape.uniform t (r + 1) hm
  let R (i : Fin t) : Representation ℂ (GeneralLinear (r + 1) E.Carrier) Y :=
    P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (r + 1)).toMonoidHom
  let I := (U).normalizedProductInduced B R
  obtain ⟨eOrbit⟩ := horbit
  rw [GeneralLinear.reindex_finCongr_rfl] at eOrbit
  change P.Equiv ((sigmaOrbitProduct σ t hm P₁).comp (MonoidHom.id _)) at eOrbit
  rw [MonoidHom.comp_id] at eOrbit
  change P.Equiv I at eOrbit
  have hRi (i : Fin t) : (R i).IsIrreducible :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff P₁ _).mpr hP₁i
  have hRq (i : Fin t) : (U).IsSquareIntegrable (R i) := by
    let e : GeneralLinear (r + 1) E.Carrier ≃ₜ* GeneralLinear (r + 1) E.Carrier :=
      { entrywiseAut (σ ^ (i : ℕ)) (r + 1) with
        continuous_toFun := continuous_entrywiseAut (σ ^ (i : ℕ)) (r + 1)
        continuous_invFun := continuous_entrywiseAut_symm (σ ^ (i : ℕ)) (r + 1) }
    exact (U).isSquareIntegrable_comp_continuousMulEquiv P₁ e hP₁q
  let D := normalizedProductSelfPairPolynomials E ψE νE B R hn hRi hRq
  let P_E : ℂ[X] := ∏ i, ∏ j, D.val i j
  have hPE : IsPadicRankLPolynomial E ψE νE.val P (smoothContragredient P) P_E :=
    (IsPadicRankLPolynomial.congr_equiv eOrbit (smoothContragredientEquiv eOrbit).symm).mpr D.property.2
  let L (κ : S) := lowerDenominator F E ψF νF hn π hπi hπs hπq ((hS _).mp κ.property)
  have hEq := hCompare P_E (fun κ => (L κ).val) hPE (fun κ => (L κ).property.1)
  have hEval : P_E.eval (((T).residueCardinality : ℂ) ^ f) ≠ 0 := by
    have h := congrArg (eval ((T).residueCardinality : ℂ)) hEq
    simp only [eval_comp, eval_pow, eval_X, eval_prod] at h
    exact h.trans_ne (Finset.prod_ne_zero_iff.mpr (fun κ _ => (L κ).property.2))
  have hUpper : P_E.eval ((U).residueCardinality : ℂ) ≠ 0 := by
    rw [hq, Nat.cast_pow]
    exact hEval
  let j : Fin t := ⟨0, ht⟩
  have hD : D.val j j ∣ P_E := (Finset.dvd_prod_of_mem (fun k => D.val j k)
    (Finset.mem_univ j)).trans (Finset.dvd_prod_of_mem (fun i => ∏ k, D.val i k) (Finset.mem_univ j))
  have hzero : R j = P₁ := by
    ext g x
    change P₁ (entrywiseAut (σ ^ 0) (r + 1) g) x = P₁ g x
    rw [pow_zero, entrywiseAut_one_apply]
  have hBlock : IsSupercuspidal P₁ := by
    have h : (D.val j j).eval ((U).residueCardinality : ℂ) ≠ 0 := by
      obtain ⟨C, hC⟩ := hD
      intro hz
      exact hUpper (by rw [hC, eval_mul, hz, zero_mul])
    have hdiag := D.property.1 j j
    change IsPadicRankLPolynomial E ψE νE.val (R j) (smoothContragredient (R j)) (D.val j j) at hdiag
    rw [hzero] at hdiag
    let A := SmoothRep.of P₁ hP₁q.isAdmissible.1
    let e := A.universeLiftEquiv.{v}
    have hAi := (isIrreducible_iff_of_equiv e).mp hP₁i
    have hAq := ((U).isSquareIntegrable_iff_of_equiv e).mp hP₁q
    have hAd := (IsPadicRankLPolynomial.congr_equiv e (smoothContragredientEquiv e).symm).mp hdiag
    exact (isSupercuspidal_iff_of_equiv e).mpr
      (isSupercuspidal_of_squareIntegrable_selfPair_eval_ne_zero E ψE νE hm A.universeLift hAi hAq hAd h)
  have horder : lPolynomialPoleOrderAtZero P_E = t := by
    have hRs (i : Fin t) : IsSupercuspidal (R i) := isSupercuspidal_comp_entrywiseAut _ _ hBlock
    let C (i : Fin t) : SupercuspidalRep.{v,uW} (F := E.Carrier) (n := r + 1) :=
      ⟨SmoothRep.of (R i) (hRs i).1.1, hRi i, hRs i⟩
    have hRu (i : Fin t) : IsUnitarizable (R i) :=
      glSquareIntegrableUnitarity p E U (r + 1) hm Y (R i) (hRi i) (hRq i)
    obtain ⟨Q, hQ, -, hQ0⟩ := unitaryCuspidalProduct_selfPair E ht ψE νE C hRu
      (sigmaConjugates_pairwise_inequivalent σ P₁ hperiod)
    have heq := D.property.2.unique hQ
    dsimp only [P_E]
    rw [heq]
    exact hQ0
  have hcount := cuspidalSelfPairDescentProfile p F E.Carrier (t * (r + 1)) hn V π hπi hπq
    ψF νF S hS (fun κ => normCharacter_isOpen_ker F E ((hS _).mp κ.property))
    f t hf P_E (fun κ => (L κ).val) (fun κ => (L κ).property.1) hEval horder hEq
  exact ⟨hBlock, hcount.2.symm⟩

end Langlands.BaseChange
