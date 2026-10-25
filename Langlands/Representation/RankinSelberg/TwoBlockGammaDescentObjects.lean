import Langlands.Representation.RankinSelberg.TwoBlockGammaRankDescent
import Langlands.Representation.RankinSelberg.TwoBlockBaseCasesStatement
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputStatement
import Langlands.Representation.RankinSelberg.EqualRankFactorSwapStatement
import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Induction.BlockEquivalence

/-! Conditional representation packaging for gamma rank descent. -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockGammaDescent

open HarmonicAnalysis Whittaker GeneralLinear

universe uF u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)

/-- Actual representations of positive rank in a carrier universe closed under
normalized induction, retaining all three full Whittaker-type conditions. -/
structure Object (r : ℕ) where
  carrier : Type (max uF u)
  addCommGroup : AddCommGroup carrier
  module : @Module ℂ carrier _ addCommGroup.toAddCommMonoid
  rep : letI := addCommGroup
    letI := module
    Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) carrier
  whittakerType : letI := F.canonicalTopologicalData.topology
    letI := addCommGroup
    letI := module
    IsOfWhittakerType r (standardCharacter ψ r) rep

attribute [instance] Object.addCommGroup Object.module

variable {F ψ}

/-- The ordered indices of a two-block induction. -/
abbrev indices (a b : ℕ) : Fin 2 → ℕ := ![a, b]

theorem indices_sum (a b : ℕ) : ∑ i, (indices a b i + 1) = (b + 1 + a) + 1 := by
  simp only [Fin.sum_univ_two, indices, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- The original representations, with their ranks matched to `indices`. -/
def family {a b : ℕ} (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b) (i : Fin 2) :
    Representation ℂ (Langlands.GeneralLinear (indices a b i + 1) F.Carrier)
      (Shahidi.pairCarrier x.carrier y.carrier i) :=
  match i with
  | 0 => x.rep
  | 1 => y.rep

theorem family_type {a b : ℕ} (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b) :
    ∀ i, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType (indices a b i) (standardCharacter ψ (indices a b i))
        (family x y i) := by
  intro i
  fin_cases i
  · exact x.whittakerType
  · exact y.whittakerType

/-- The actual canonical normalized induction, bundled with full type obtained
from the explicit preservation premise. -/
def induced (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    {a b : ℕ} (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b) : Object.{uF, u} F ψ (b + 1 + a) where
  carrier := _
  addCommGroup := inferInstance
  module := inferInstance
  rep := F.canonicalNormalizedProductInduced (succBlockShape (indices a b) (indices_sum a b))
    (family x y)
  whittakerType := hInd p F ψ (b + 1 + a) 2 (indices a b) (indices_sum a b)
    (family x y) (family_type x y)

variable (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)

/-- A chosen certified unit. The analytic construction input is an explicit
premise, rather than a claim of unconditional gamma existence. -/
def gamma
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    {r t : ℕ} (x : Object.{uF, u} F ψ r) (y : Object.{uF, u} F ψ t) : RationalFunctionsˣ :=
  (padicSymmetricGammaFactorOfWhittakerType F ψ ν.val x.rep y.rep
    (hInput p F ψ ν r t x.carrier y.carrier x.rep y.rep
      x.whittakerType y.whittakerType)).val

theorem gamma_cert
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    {r t : ℕ} (x : Object.{uF, u} F ψ r) (y : Object.{uF, u} F ψ t) :
    IsPadicSymmetricGammaFactor F ψ ν.val x.rep y.rep
      (gamma ν hInput x y : RationalFunctions) :=
  (padicSymmetricGammaFactorOfWhittakerType F ψ ν.val x.rep y.rep
    (hInput p F ψ ν r t x.carrier y.carrier x.rep y.rep
      x.whittakerType y.whittakerType)).property

/-- Equal-rank exchange is supplied by its explicit analytic premise. In
unequal ranks the larger-rank-first predicate gives exchange definitionally. -/
theorem certificate_swap
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    {r t : ℕ} (x : Object.{uF, u} F ψ r) (y : Object.{uF, u} F ψ t) {G : RationalFunctions}
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val x.rep y.rep G) :
    IsPadicSymmetricGammaFactor F ψ ν.val y.rep x.rep G := by
  rcases lt_trichotomy r t with h | h | h
  · simpa only [IsPadicSymmetricGammaFactor, Nat.not_le.mpr h, Nat.le_of_lt h,
      ite_false, ite_true] using hG
  · subst t
    have hEq := (hSwap p F ψ ν r x.rep y.rep x.whittakerType y.whittakerType).2.2 G
    have hPair : IsPadicPairGammaFactor F ψ ν.val x.rep y.rep G := by
      simpa only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true] using hG
    simpa only [IsPadicSymmetricGammaFactor, Nat.le_refl, ite_true] using
      hEq.mp hPair
  · simpa only [IsPadicSymmetricGammaFactor, Nat.not_le.mpr h, Nat.le_of_lt h,
      ite_false, ite_true] using hG

theorem gamma_swap
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    {r t : ℕ} (x : Object.{uF, u} F ψ r) (y : Object.{uF, u} F ψ t) :
    gamma ν hInput x y = gamma ν hInput y x := by
  apply Units.ext
  exact (certificate_swap ν hSwap x y (gamma_cert ν hInput x y)).unique
    (gamma_cert ν hInput y x)


/-- Uniqueness changes a certified finite product into an equality between the
chosen units. This uses no analytic argument. -/
theorem equality_of_certificates
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    {r a b : ℕ} (pi : Object.{uF, u} F ψ r)
    (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b)
    (h : ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val pi.rep (family x y i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val pi.rep (induced hInd x y).rep (∏ i, G i)) :
    gamma ν hInput pi (induced hInd x y) = gamma ν hInput pi x * gamma ν hInput pi y := by
  obtain ⟨G, hG, hProd⟩ := h
  have h0 := (hG 0).unique (gamma_cert ν hInput pi x)
  have h1 := (hG 1).unique (gamma_cert ν hInput pi y)
  apply Units.ext
  simpa only [Fin.prod_univ_two, h0, h1, Units.val_mul] using
    (gamma_cert ν hInput pi (induced hInd x y)).unique hProd

theorem dominant_eq
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hDominant : TwoBlockGammaDominantRankStatement.{uF, max uF u, max uF u})
    {r a b : ℕ} (pi : Object.{uF, u} F ψ r)
    (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b) (hr : b + 1 + a ≤ r) :
    gamma ν hInput pi (induced hInd x y) = gamma ν hInput pi x * gamma ν hInput pi y :=
  equality_of_certificates ν hInd hInput pi x y
    (hDominant p F ψ ν r (b + 1 + a) (indices a b) (indices_sum a b)
      pi.rep (family x y) hr pi.whittakerType (family_type x y))

theorem adjacent_eq
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hAdjacent : TwoBlockGammaAdjacentRankStatement.{uF, max uF u, max uF u})
    {r : ℕ} (pi : Object.{uF, u} F ψ r)
    (x : Object.{uF, u} F ψ 0) (y : Object.{uF, u} F ψ r) :
    gamma ν hInput pi (induced hInd x y) = gamma ν hInput pi x * gamma ν hInput pi y :=
  equality_of_certificates ν hInd hInput pi x y
    (hAdjacent p F ψ ν r (r + 1) (indices 0 r) (indices_sum 0 r)
      pi.rep (family x y) rfl rfl pi.whittakerType (family_type x y))

theorem rankOne_eq
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hRankOne : TwoBlockGammaRankOneStatement.{uF, max uF u, max uF u})
    {a b : ℕ} (pi : Object.{uF, u} F ψ 0)
    (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b) :
    gamma ν hInput pi (induced hInd x y) = gamma ν hInput pi x * gamma ν hInput pi y :=
  equality_of_certificates ν hInd hInput pi x y
    (hRankOne p F ψ ν 0 (b + 1 + a) (indices a b) (indices_sum a b)
      pi.rep (family x y) rfl pi.whittakerType (family_type x y))

/-- The two-stage algebra is instantiated on actual full-type representations
and certified units. Every analytic result remains an explicit premise. -/
theorem allRanks_eq
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (hDominant : TwoBlockGammaDominantRankStatement.{uF, max uF u, max uF u})
    (hAdjacent : TwoBlockGammaAdjacentRankStatement.{uF, max uF u, max uF u})
    (hRankOne : TwoBlockGammaRankOneStatement.{uF, max uF u, max uF u})
    (mu : Object.{uF, u} F ψ 0) :
    ∀ {r a b : ℕ} (pi : Object.{uF, u} F ψ r)
      (x : Object.{uF, u} F ψ a) (y : Object.{uF, u} F ψ b),
      gamma ν hInput pi (induced hInd x y) = gamma ν hInput pi x * gamma ν hInput pi y :=
  twoBlockGammaRankDescent
    (ind := @induced _ _ F ψ hInd) (gamma := @gamma _ _ F ψ ν hInput)
    (mu := mu) (swap := @gamma_swap _ _ F ψ ν hInput hSwap)
    (@dominant_eq _ _ F ψ ν hInd hInput hDominant)
    (@adjacent_eq _ _ F ψ ν hInd hInput hAdjacent)
    (@rankOne_eq _ _ F ψ ν hInd hInput hRankOne)


/-- Bundle an original full-type representation without changing its action. -/
def ofRepresentation {r : ℕ} {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
    (pi : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hpi : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) pi) : Object.{uF, u} F ψ r :=
  ⟨V, inferInstance, inferInstance, pi, hpi⟩

set_option maxHeartbeats 1600000 in
/-- Conditional all-rank multiplicativity for the target's arbitrary dependent
ordered block family, using an actual induced-representation equivalence. -/
theorem certified
    (hInd : NormalizedProductWhittakerTypeStatement.{uF, max uF u})
    (hInput : WhittakerTypeGammaConstructionInputStatement.{uF, max uF u, max uF u})
    (hSwap : EqualRankFactorSwapStatement.{uF, max uF u, max uF u})
    (hDominant : TwoBlockGammaDominantRankStatement.{uF, max uF u, max uF u})
    (hAdjacent : TwoBlockGammaAdjacentRankStatement.{uF, max uF u, max uF u})
    (hRankOne : TwoBlockGammaRankOneStatement.{uF, max uF u, max uF u})
    (mu : Object.{uF, u} F ψ 0)
    (r t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Type (max uF u)} [AddCommGroup V] [Module ℂ V]
    {W : Fin 2 → Type (max uF u)} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (pi : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (sigma : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (W i))
    (hpi : letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType r (standardCharacter ψ r) pi)
    (hsigma : ∀ i, letI := F.canonicalTopologicalData.topology
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (sigma i)) :
    ∃ G : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val pi (sigma i) (G i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val pi
        (F.canonicalNormalizedProductInduced (succBlockShape m h) sigma) (∏ i, G i) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, m = indices a b := by
    refine ⟨m 0, m 1, ?_⟩
    funext i
    fin_cases i <;> rfl
  have ht : t = b + 1 + a := by
    simp only [Fin.sum_univ_two, indices, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    omega
  subst t
  let P := ofRepresentation pi hpi
  let X : ∀ i, Object.{uF, u} F ψ (indices a b i) :=
    fun i => ofRepresentation (sigma i) (hsigma i)
  let G : Fin 2 → RationalFunctions := fun i => (gamma ν hInput P (X i) : RationalFunctions)
  refine ⟨G, fun i => gamma_cert ν hInput P (X i), ?_⟩
  have he : ∀ i, (family (X 0) (X 1) i).Equiv (sigma i) := by
    intro i
    match i with
    | 0 => exact Representation.Equiv.refl _
    | 1 => exact Representation.Equiv.refl _
  have eInd := F.canonicalTopologicalData.normalizedProductInducedEquiv
    (succBlockShape (indices a b) h) he
  apply (IsPadicSymmetricGammaFactor.congr_equiv (Representation.Equiv.refl pi) eInd).mp
  change IsPadicSymmetricGammaFactor F ψ ν.val P.rep
    (induced hInd (X 0) (X 1)).rep (∏ i, G i)
  have hMult := allRanks_eq ν hInd hInput hSwap hDominant hAdjacent hRankOne mu P (X 0) (X 1)
  have hCert := gamma_cert ν hInput P (induced hInd (X 0) (X 1))
  rw [hMult] at hCert
  simpa only [Fin.prod_univ_two, Units.val_mul, G] using hCert

end Langlands.RankinSelberg.TwoBlockGammaDescent
