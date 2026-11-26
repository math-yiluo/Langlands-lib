import Langlands.BaseChange.PadicSquareIntegrableNotInduced
import Langlands.Representation.Classification.SquareIntegrableGenericityProof
import Langlands.Representation.Classification.SquareIntegrableUnitarityProof
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.CuspidalSupport.RationalSummandEndCenterReduction
import Langlands.Representation.RankinSelberg.PadicSymmetricLFactor
import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLFactorProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.SupercuspidalPairPoleOrder
import Langlands.Representation.RankinSelberg.UniformRankOneTwistProof

/-! # Certified twisted self-pair polynomials of discrete series -/

noncomputable section

namespace Langlands.RankinSelberg

open Classification GeneralLinear HarmonicAnalysis LocalFactor Polynomial Whittaker

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local notation "T" => F.canonicalTopologicalData
local instance twistedSelfPairTopology : TopologicalSpace F.Carrier := (T).topology
local instance twistedSelfPairValuativeRel : ValuativeRel F.Carrier := (T).valuativeRel
local instance twistedSelfPairLocalField : IsNonarchimedeanLocalField F.Carrier := (T).localField
local instance twistedSelfPairGroupTopology (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  (T).generalLinearTopologicalGroup n

private theorem isGeneric_of_squareIntegrable_action
    (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hi : π.IsIrreducible) (hsq : (T).IsSquareIntegrable π) : IsGeneric ψ r π := by
  let A := SmoothRep.of π hsq.isAdmissible.1
  let e := A.universeLiftEquiv.{uF}
  have hi' := (isIrreducible_iff_of_equiv e).mp hi
  have hsq' := ((T).isSquareIntegrable_iff_of_equiv e).mp hsq
  have hu := glSquareIntegrableUnitarity p F (T) (r + 1) (Nat.succ_pos r) _ _ hi' hsq'
  exact (isGeneric_iff_of_equiv ψ r e).mpr
    (squareIntegrableGenericity.{uF,uV} F (T) r A.universeLift hi' hsq' hu ψ)

/-- The pair of a square-integrable irreducible with a smooth determinant twist of
its smooth dual has a certified L-polynomial. -/
theorem exists_twistedSelfPairPolynomial
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : PadicAbelian.SelfDualHaar (T) ψ)
    {n : ℕ} (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V)
    (hi : π.IsIrreducible) (hsq : (T).IsSquareIntegrable π)
    (κ : F.Carrierˣ →* ℂˣ) (hκ : IsOpen (κ.ker : Set F.Carrierˣ)) :
    ∃ Q : ℂ[X], IsPadicRankLPolynomial F ψ ν.val π
      (twist (κ.comp determinant) (smoothContragredient π)) Q := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let A := SmoothRep.of π hsq.isAdmissible.1
  let ξ : Quasicharacter F.Carrier :=
    { κ with continuous_toFun := CuspidalSupport.NormalHecke.continuous_of_isOpen_ker κ hκ }
  have hid := (A.isIrreducible_contragredient_iff (compactOpen_cofinal F (T) (r + 1))
    hsq.isAdmissible).mpr hi
  have hsq' := (T).isSquareIntegrable_smoothContragredient π hsq
  have hg := isGeneric_of_squareIntegrable_action F ψ π hi hsq
  have hgd := isGeneric_of_squareIntegrable_action F ψ (smoothContragredient π) hid hsq'
  have hgt := UniformRankOneTwist.isGeneric_twist F ψ (smoothContragredient π) hgd ξ
  exact ⟨_, (isPadicRankLPolynomial_succ.mpr
    (genericSymmetricLPolynomial_isPadic F ψ ν.val π _ hg hgt))⟩

open Classical in
/-- A twisted self-pair of a supercuspidal has a pole at zero precisely when the
determinant twist fixes its class. The contributing pole is simple. -/
theorem lPolynomialPoleOrderAtZero_twistedSelfPair_supercuspidal
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : PadicAbelian.SelfDualHaar (T) ψ)
    {n : ℕ} (hn : 0 < n) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F.Carrier) V) (hi : π.IsIrreducible)
    (hsc : IsSupercuspidal π) (κ : F.Carrierˣ →* ℂˣ)
    (hκ : IsOpen (κ.ker : Set F.Carrierˣ)) {Q : ℂ[X]}
    (hQ : IsPadicRankLPolynomial F ψ ν.val π (twist (κ.comp determinant) (smoothContragredient π)) Q) :
    lPolynomialPoleOrderAtZero Q = if Nonempty (π.Equiv (twist (κ.comp determinant) π))
      then 1 else 0 := by
  classical
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let χ := κ.comp (determinant (R := F.Carrier) (n := r + 1))
  have hχ : IsOpen (χ.ker : Set (GeneralLinear (r + 1) F.Carrier)) :=
    hκ.preimage determinantContinuous.continuous
  let A := SmoothRep.of π hsc.1.1
  let ρ := twist χ (smoothContragredient π)
  have hid := (A.isIrreducible_contragredient_iff (compactOpen_cofinal F (T) (r + 1)) hsc.1).mpr hi
  have hiρ := (isIrreducible_twist_iff χ _).mpr hid
  have hscd := isSupercuspidal_smoothContragredient F (T) (r + 1) V π hsc
  have hscρ := (isSupercuspidal_twist_iff χ hχ (ker_determinant_le_ker_comp κ) _).mpr hscd
  have hw := SupercuspidalLFactorCharacterization.isOfWhittakerType_of_isSupercuspidal F ψ r
    (SmoothRep.of ρ hscρ.1.1) hiρ hscρ
  rw [lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank supercuspidalEqualRankLFactor ν
    hi hsc hiρ hw ((isPadicSymmetricLPolynomial_of_le le_rfl).mp (isPadicRankLPolynomial_succ.mp hQ)),
    contragredientIndicator]
  refine if_congr ?_ rfl rfl
  have hb := (smoothBidual hsc.1.1).ofBijective
    (((smoothAdmissibleDuality (compactOpen_cofinal F (T) (r + 1))).2 π hsc.1).2)
  let ed := (smoothContragredientTwistEquiv χ (smoothContragredient π) hχ).trans
    (twistEquiv χ⁻¹ hb.symm)
  constructor
  · rintro ⟨e⟩
    have et := twistEquiv χ (e.trans ed)
    rw [twist_twist_inv] at et
    exact ⟨et.symm⟩
  · rintro ⟨e⟩
    have et := twistEquiv χ⁻¹ e
    rw [twist_inv_twist] at et
    exact ⟨et.symm.trans ed.symm⟩

end Langlands.RankinSelberg
