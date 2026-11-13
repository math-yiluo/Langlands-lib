import Langlands.Correspondence.SphericalTemperedStandardModuleProof
import Langlands.Correspondence.RankOneAnalyticLFactor
import Langlands.Correspondence.RankOneAnalyticGaussEpsilon
import Langlands.Correspondence.AutomorphicPairFactors
import Langlands.Representation.RankinSelberg.SquareIntegrableDataLFactorProof
import Langlands.Representation.RankinSelberg.SquareIntegrableDataPoleOrder
import Langlands.Representation.RankinSelberg.TemperedTwistSupercuspidalPoleClassification
import Langlands.Representation.Classification.UnitaryExponentScalarNormProof
import Langlands.Representation.Unramified.HeckeComparisonProof
import Langlands.Global.Factors.HeckeFiniteEpsilon

/-! # Pair factors of spherical representations -/

noncomputable section

set_option autoImplicit false

open Polynomial

namespace Langlands.Correspondence

open GeneralLinear Unramified

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance unramifiedPairFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance unramifiedPairGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance unramifiedPairGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

section Block

/-- The rank-one block of the unramified character with uniformizer value `z`. -/
abbrev unramifiedBlock (z : ℂˣ) : SmoothRep.{0, uF, uA} ℂ (GeneralLinear 1 F.Carrier) :=
  (rankOneSupercuspidalObject.{uF, uA} F (character F z)).obj

theorem unramifiedBlock_isIrreducible (z : ℂˣ) :
    Representation.IsIrreducible (unramifiedBlock.{uF, uA} F z).representation :=
  (rankOneSupercuspidalObject.{uF, uA} F (character F z)).property.1

theorem unramifiedBlock_isEssentiallySquareIntegrable (z : ℂˣ) :
    F.canonicalTopologicalData.IsEssentiallySquareIntegrable
      (unramifiedBlock.{uF, uA} F z).representation :=
  RankinSelberg.supercuspidal_isEssentiallySquareIntegrable F 0 _
    (unramifiedBlock_isIrreducible F z)
    (rankOneSupercuspidalObject.{uF, uA} F (character F z)).property.2

/-- The uniformizer as an element of `GL_1(F)`. -/
abbrev uniformizerElement : GeneralLinear 1 F.Carrier :=
  scalar F.canonicalTopologicalData.uniformizerUnit

theorem determinant_uniformizerElement :
    determinant (uniformizerElement F) = F.canonicalTopologicalData.uniformizerUnit := by
  ext
  simp [uniformizerElement, scalar]

theorem unramifiedBlock_uniformizerElement (z : ℂˣ) (v : unramifiedBlock.{uF, uA} F z) :
    (unramifiedBlock.{uF, uA} F z).representation (uniformizerElement F) v = (z : ℂ) • v := by
  change ((character F z (determinant (uniformizerElement F)) : ℂˣ) : ℂ) • v = (z : ℂ) • v
  rw [determinant_uniformizerElement, character_uniformizer]

/-- Every unitary exponent of the block of `z` is `log_|ϖ| ‖z‖`: the uniformizer
acts by `z`, so `‖z‖ = |ϖ|^α`. -/
theorem norm_eq_rpow_unitaryExponent (z : ℂˣ)
    (u : UnitaryExponentData (F.canonicalTopologicalData.determinantNorm 1)
      (unramifiedBlock.{uF, uA} F z).representation) :
    ‖(z : ℂ)‖ = F.canonicalTopologicalData.normalizedAbs
      F.canonicalTopologicalData.uniformizer ^ u.exponent := by
  have : Nontrivial (unramifiedBlock.{uF, uA} F z) := by
    change Nontrivial (ULift.{uA} ℂ)
    infer_instance
  have h := unitaryExponentScalarNorm.{uF, uA} (GeneralLinear 1 F.Carrier)
    (unramifiedBlock.{uF, uA} F z) _ _ u (uniformizerElement F) (z : ℂ)
    (unramifiedBlock_uniformizerElement F z)
  rw [h, PadicField.TopologicalData.determinantNorm_coe, determinant_uniformizerElement]
  rfl

/-- The character of `w * w'` is the product of the characters of `w` and `w'`. -/
theorem character_mul (w w' : ℂˣ) : character F w * character F w' = character F (w * w') := by
  ext a
  simp [character_apply, mul_zpow]

/-- An unramified character has multiplicative conductor zero. -/
theorem multiplicativeConductor_character (w : ℂˣ) :
    F.canonicalTopologicalData.multiplicativeConductor (character F w) = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  apply (F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le _ 0).mp
  intro u hu
  have hl := (LocalFactor.PadicAbelian.unitLevel_iff_mem_principalUnits
    F.canonicalTopologicalData 0 u).mpr hu
  simp only [LocalFactor.PadicAbelian.unitLevel, ite_true] at hl
  change F.canonicalTopologicalData.unramifiedCharacter w u = 1
  rw [PadicField.TopologicalData.unramifiedCharacter_apply, hl, zpow_zero]

/-- Tate's L-polynomial of an unramified character `χ_w` is `1 - w X`. -/
theorem lPolynomial_character (w : ℂˣ) :
    LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData (character F w) =
      1 - C (w : ℂ) * X := by
  simp only [LocalFactor.PadicAbelian.lPolynomial, multiplicativeConductor_character,
    ↓reduceIte]
  rw [character_apply, LocalFactor.PadicAbelian.uniformizerUnit_ord, zpow_one]

variable {F} in
/-- The L-polynomial of the pair of unramified blocks of `w` and `w'` is `1 - w w' X`. -/
theorem unramifiedBlock_lPolynomial_eq (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (w w' : ℂˣ) {Q : ℂ[X]}
    (hQ : RankinSelberg.IsPadicRankLPolynomial F ψ ν
      (unramifiedBlock.{uF, uA} F w).representation
      (unramifiedBlock.{uF, uA} F w').representation Q) :
    Q = 1 - C ((w : ℂ) * w') * X := by
  have h0 : RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
      (unramifiedBlock.{uF, uA} F w).representation
      (unramifiedBlock.{uF, uA} F w').representation
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData
        (character F w * character F w')) :=
    (RankinSelberg.isPadicSymmetricLPolynomial_of_le (Nat.le_refl 0)).mpr
      (isPadicPairLPolynomial_of_rankOneCharacterEquiv F ψ ν
        (FiniteRepresentation.characterLineEquiv.{uF, uA}
          (determinantQuasiCharacter F 1 (character F w))).symm
        (FiniteRepresentation.characterLineEquiv.{uF, uA}
          (determinantQuasiCharacter F 1 (character F w'))).symm)
  have h1 : RankinSelberg.IsPadicSymmetricLPolynomial F ψ ν
      (unramifiedBlock.{uF, uA} F w).representation
      (unramifiedBlock.{uF, uA} F w').representation Q :=
    RankinSelberg.isPadicRankLPolynomial_succ.mp hQ
  rw [h1.unique h0, character_mul, lPolynomial_character, Units.val_mul]

variable {F} in
/-- For `ψ` of conductor zero and `ν` self-dual, the epsilon factor of the pair of
unramified blocks of `w` and `w'` is `(1, 0)`. -/
theorem unramifiedBlock_epsilonFactor_eq (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0) (w w' : ℂˣ) {b : ℂˣ × ℤ}
    (hb : RankinSelberg.IsPadicRankEpsilonFactor F ψ ν
      (unramifiedBlock.{uF, uA} F w).representation
      (unramifiedBlock.{uF, uA} F w').representation b) :
    b = (1, 0) := by
  have h0 := isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss F ψ ν hν
    (χ := character F w) (η := character F w')
    (FiniteRepresentation.characterLineEquiv.{uF, uA}
      (determinantQuasiCharacter F 1 (character F w))).symm
    (FiniteRepresentation.characterLineEquiv.{uF, uA}
      (determinantQuasiCharacter F 1 (character F w'))).symm
  have h1 := (RankinSelberg.isPadicSymmetricEpsilonFactor_of_le (Nat.le_refl 0)).mp
    (RankinSelberg.isPadicRankEpsilonFactor_succ.mp hb)
  rw [h1.unique h0, character_mul]
  refine Prod.ext (Units.ext ?_) ?_
  · rw [GodementJacquet.Padic.coe_tateEpsilonCoefficient, Units.val_one]
    exact Global.HeckeFunctionalEquation.epsilon_eq_one_of_conductors_eq_zero
      F.canonicalTopologicalData (character F (w * w')) ψ ⟨ν, hν⟩
      (multiplicativeConductor_character F (w * w')) hψ 0
  · change (F.canonicalTopologicalData.multiplicativeConductor (character F (w * w')) : ℤ) +
      F.canonicalTopologicalData.additiveConductor ψ = 0
    rw [multiplicativeConductor_character, hψ]
    rfl

end Block

section Datum

variable {r : ℕ}

/-- A chosen unitary exponent of the block of `w`. -/
def unramifiedExponentData (w : ℂˣ) :
    UnitaryExponentData (F.canonicalTopologicalData.determinantNorm 1)
      (unramifiedBlock.{uF, uA} F w).representation :=
  (F.canonicalTopologicalData.nonempty_unitaryExponentData Nat.one_pos
    (unramifiedBlock_isIrreducible F w) (unramifiedBlock_isEssentiallySquareIntegrable F w)).some

/-- The essentially square-integrable datum `(χ_(z_1), …, χ_(z_(r+1)))` on the Borel
shape, for norms weakly increasing (so exponents weakly decreasing). -/
def unramifiedDatum (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖) :
    PadicField.TopologicalData.SquareIntegrableLanglandsDatum.{uA, uF}
      F.canonicalTopologicalData (r + 1) where
  shape := borelShape r
  blocks i := unramifiedBlock.{uF, uA} F (z i)
  irreducible i := unramifiedBlock_isIrreducible F (z i)
  essentiallySquareIntegrable i := unramifiedBlock_isEssentiallySquareIntegrable F (z i)
  unitaryExponent i := unramifiedExponentData F (z i)
  antitone i j hij := by
    obtain ⟨hb0, hb1⟩ := uniformizer_norm_bounds F
    have h : ‖(z i : ℂ)‖ ≤ ‖(z j : ℂ)‖ := hz hij
    rw [norm_eq_rpow_unitaryExponent F (z i) (unramifiedExponentData F (z i)),
      norm_eq_rpow_unitaryExponent F (z j) (unramifiedExponentData F (z j))] at h
    exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hb1).mp h

/-- The induced representation of `unramifiedDatum z` is the principal series of `z`. -/
def unramifiedDatumInducedEquiv (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖) :
    (unramifiedDatum.{uF, uA} F z hz).induced.representation.Equiv
      (principalSeriesOfTuple F z) := by
  unfold principalSeriesOfTuple principalSeries characterTuple
  refine F.canonicalTopologicalData.normalizedProductInducedEquiv (borelShape r) (fun i => ?_)
  exact Representation.Equiv.mk ULift.moduleEquiv (fun g => by ext v; rfl)

/-- A spherical representation with spectrum `s` is a Langlands quotient of
`unramifiedDatum z` for an ordering `z` of `s` with weakly increasing norms. -/
theorem exists_unramifiedDatum_isLanglandsQuotient
    (A : AutomorphicObject.{uF, uA} F r.succPNat)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (e : J.representation.Equiv A.obj.representation) (s : Eigenvalues (r + 1))
    (hs : HasSphericalSpectrum F A s) :
    ∃ (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖),
      Eigenvalues.ofTuple z = s ∧ (unramifiedDatum.{uF, uA} F z hz).IsLanglandsQuotient J := by
  obtain ⟨d, z, hd, hzs, hz, ⟨f⟩⟩ := sphericalTemperedStandardModule.{uF, uA} F r A J s ⟨e⟩ hs
  obtain ⟨hJ, q, hq⟩ := hd
  let g := (unramifiedDatumInducedEquiv F z hz).trans f.symm
  exact ⟨z, hz, hzs, hJ, q.comp g.toIntertwiningMap, hq.comp g.surjective⟩

end Datum

section Pairs

variable {r t : ℕ}

/-- The pair L-polynomial of Langlands quotients of `unramifiedDatum z` and
`unramifiedDatum z'` is `∏_(i,j) (1 - z_i z'_j X)`. -/
theorem unramifiedDatum_lPolynomial_eq (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖)
    (z' : Fin (t + 1) → ℂˣ) (hz' : Monotone fun i => ‖(z' i : ℂ)‖)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (hd : (unramifiedDatum.{uF, uA} F z hz).IsLanglandsQuotient J)
    (hd' : (unramifiedDatum.{uF, uA} F z' hz').IsLanglandsQuotient J') {P : ℂ[X]}
    (hP : RankinSelberg.IsLanglandsPairLPolynomial.{uF, uA, uA} F ψ ν J J' P) :
    P = ∏ i, ∏ j, (1 - C ((z i : ℂ) * z' j) * X) := by
  obtain ⟨P0, Q, hP0, hQ, hPQ⟩ := RankinSelberg.squareIntegrableDataLFactor.{uF, uA, uA}
    p F ψ ⟨ν, hν⟩ r t (unramifiedDatum.{uF, uA} F z hz) (unramifiedDatum.{uF, uA} F z' hz')
    J J' hd hd'
  rw [hP.unique hP0, hPQ]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ =>
    unramifiedBlock_lPolynomial_eq ψ ν (z i) (z' j) (hQ i j)

/-- For `ψ` of conductor zero and `ν` self-dual, the pair epsilon factor of
Langlands quotients of `unramifiedDatum z` and `unramifiedDatum z'` is `(1, 0)`. -/
theorem unramifiedDatum_epsilonFactor_eq (ψ : NontrivialAdditiveCharacter F)
    (ν : LocalAdditiveHaarMeasure F) (hν : IsSelfDualMeasure F ψ ν)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0)
    (z : Fin (r + 1) → ℂˣ) (hz : Monotone fun i => ‖(z i : ℂ)‖)
    (z' : Fin (t + 1) → ℂˣ) (hz' : Monotone fun i => ‖(z' i : ℂ)‖)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (r + 1) F.Carrier))
    (J' : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (t + 1) F.Carrier))
    (hd : (unramifiedDatum.{uF, uA} F z hz).IsLanglandsQuotient J)
    (hd' : (unramifiedDatum.{uF, uA} F z' hz').IsLanglandsQuotient J') {e : ℂˣ × ℤ}
    (he : RankinSelberg.IsLanglandsPairEpsilonFactor.{uF, uA, uA} F ψ ν J J' e) :
    e = (1, 0) := by
  obtain ⟨b, hb, rfl⟩ := he.2.2 _ _ hd hd'
  have hb1 : ∀ i j, b i j = (1, 0) := fun i j =>
    unramifiedBlock_epsilonFactor_eq ψ ν hν hψ (z i) (z' j) (hb i j)
  simp [RankinSelberg.epsilonFactorProduct, hb1]

end Pairs

end Langlands.Correspondence
