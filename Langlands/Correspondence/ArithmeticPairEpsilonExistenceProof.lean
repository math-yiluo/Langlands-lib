import Langlands.Correspondence.ArithmeticPairEpsilonExistenceStatement
import Langlands.Correspondence.ArithmeticEpsilonDirectSum
import Langlands.Correspondence.RankOneEpsilonFieldTransport
import Langlands.Correspondence.RankOneArithmeticEpsilonData
import Langlands.LocalFactor.SpectralConductorReduction
import Langlands.LocalFactor.SpectralConductorRankOneProof
import Langlands.LocalFactor.Ramification.InertiaConductorRefinementProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof
import Langlands.Weil.Representation.InductionContinuity
import Langlands.Weil.Representation.SubquotientContinuity

/-!
# Existence of arithmetic pair epsilon factors

Proof of `ArithmeticPairEpsilonExistenceStatement`. The bottom-field datum is the
transported character, the transported self-dual measure, and the restrictions of
continuous representatives with carriers moved to coordinates in the pair universe.
Tate's (3.4.5) (`SpectralConductorStatement`, proved from its rank-one reduction)
gives `ε(V ω_s) = ε(V) q^(-r s)`; the exponent `r` is an integer because the spectral
twist depends on `s` only through `q^(-s)`. The Weil–Deligne correction is a
monomial in `q^(-s)` by definition.
-/

noncomputable section

universe u uV uE uG uW

namespace Langlands.WeilDeligneRepresentation

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- Transport of a pair along a linear isomorphism of its carrier: the action and the
monodromy are conjugated by the isomorphism. -/
def transportCarrier (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (e : A ≃ₗ[ℂ] W) :
    WeilDeligneRepresentation.{0, uG, uW} ℂ G ν :=
  haveI : Module.Finite ℂ W := Module.Finite.equiv e
  { toFiniteRepresentation :=
      FiniteRepresentation.of
        ((e.conjAlgEquiv ℂ).toRingEquiv.toMonoidHom.comp A.representation)
    monodromy := e.conjAlgEquiv ℂ A.monodromy
    nilpotent := A.nilpotent.map (e.conjAlgEquiv ℂ)
    covariance := fun g => by
      change e.conjAlgEquiv ℂ (A.representation g) * e.conjAlgEquiv ℂ A.monodromy *
        e.conjAlgEquiv ℂ (A.representation g⁻¹) = (ν g : ℂ) • e.conjAlgEquiv ℂ A.monodromy
      rw [← map_mul, ← map_mul, A.covariance g, map_smul] }

/-- The transporting isomorphism is an equivalence of pairs. -/
def transportCarrierEquiv (A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] (e : A ≃ₗ[ℂ] W) :
    Equiv A (transportCarrier A e) where
  representationEquiv := Representation.Equiv.mk e (fun g => by
    ext v
    change e (A.representation g v) = e (A.representation g (e.symm (e v)))
    rw [LinearEquiv.symm_apply_apply])
  comm_monodromy := by
    ext v
    change e (A.monodromy v) = e (A.monodromy (e.symm (e v)))
    rw [LinearEquiv.symm_apply_apply]

end Langlands.WeilDeligneRepresentation

namespace Langlands.Correspondence

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureSpectral
  LocalFactor.CommonClosureWeilDeligne

namespace ArithmeticPairEpsilonExistence

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{u} p)

/-- The restriction of a local pair to the bottom field, on the coordinate carrier
`ULift (Fin n → ℂ)` in the universe of common-closure pairs. -/
def basePair (B : LocalWeilDeligneRepresentation.{u, uV} K) :
    Pair.{u, uE} K (baseExtension K) :=
  WeilDeligneRepresentation.transportCarrier
    (WeilDeligneRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype B)
    ((Module.finBasis ℂ B).equivFun.trans
      (ULift.moduleEquiv : ULift.{max u uE} (Fin (Module.finrank ℂ B) → ℂ) ≃ₗ[ℂ] _).symm)

/-- The bottom-field pair is equivalent to the restriction. -/
def basePairEquiv (B : LocalWeilDeligneRepresentation.{u, uV} K) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup K (baseExtension K)).subtype B)
      (basePair.{u, uV, uE} K B) :=
  WeilDeligneRepresentation.transportCarrierEquiv _ _

theorem basePair_isBaseRestriction (B : LocalWeilDeligneRepresentation.{u, uV} K) :
    IsBaseRestriction K (WeilDeligneRepresentation.classOf B) (basePair.{u, uV, uE} K B) :=
  ⟨B, rfl, ⟨basePairEquiv K B⟩⟩

theorem basePair_isContinuous {B : LocalWeilDeligneRepresentation.{u, uV} K}
    (hB : B.toFiniteRepresentation.IsContinuous) :
    (basePair.{u, uV, uE} K B).toFiniteRepresentation.IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv (basePairEquiv K B).representationEquiv).mp
    (FiniteRepresentation.isContinuous_restrict _ continuous_subtype_val hB)

/-- The spectral twist depends on `s` only through `q^(-s)`. -/
theorem virtualTwist_eq_of_spectralParameter_eq (E : Extension K) {s t : ℂ}
    (h : spectralParameter (baseCardinality K) (baseCardinality_pos K) s =
      spectralParameter (baseCardinality K) (baseCardinality_pos K) t) :
    virtualTwist.{u, uE} K E s = virtualTwist.{u, uE} K E t := by
  unfold virtualTwist SpectralTwist.virtual SpectralTwist.character
  rw [h]

/-- An exponent `r` with `q^(-r · 2πi / log q) = 1` is an integer. -/
theorem exists_int_of_cpow_period {q : ℝ} (hq : 1 < q) {r : ℂ}
    (h : (q : ℂ) ^ (-r * (2 * Real.pi * Complex.I / (Real.log q : ℂ))) = 1) :
    ∃ k : ℤ, r = k := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hlog : (Real.log q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.ofReal_log (by linarith)] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨-n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (Real.log q : ℂ) * (-r * (2 * Real.pi * Complex.I / (Real.log q : ℂ))) =
      -r * (2 * Real.pi * Complex.I) := by
    field_simp
  rw [this] at hn
  have := mul_right_cancel₀ h2 hn
  push_cast
  linear_combination -this

/-- The residue cardinality of `K` as a natural number. -/
local notation "qK" => K.canonicalTopologicalData.residueCardinality

/-- The residue cardinality exceeds `1`. -/
theorem one_lt_baseCardinality : 1 < baseCardinality K := by
  change (1 : ℝ) < (qK : ℝ)
  exact_mod_cast K.canonicalTopologicalData.residueCardinality_gt_one

/-- Tate (3.4.5) with an integer exponent: the Deligne value of a continuous
representation of the bottom Weil group is its value at `0` times an integral power of
`q^(-s)`. -/
theorem conditionalDeligneValue_monomial (e : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{u, uE} K) (hε : NonabelianSystem.IsSystem K e ε)
    (ψ : AdditiveCharacter K (ConductorExponent.base K))
    (μ : HaarMeasure K (ConductorExponent.base K))
    (A : FiniteRepresentation.{0, u, max u uE} ℂ (weilSubgroup K (ConductorExponent.base K)))
    (hA : A.IsContinuous) :
    ∃ k : ℤ, ∀ s : ℂ,
      (conditionalDeligneValue K e ε hε (ConductorExponent.base K) ψ μ
          (ConductorExponent.baseClass K A hA) s : ℂ) =
        (conditionalDeligneValue K e ε hε (ConductorExponent.base K) ψ μ
          (ConductorExponent.baseClass K A hA) 0 : ℂ) *
          RankinSelberg.spectralPoint qK s ^ k := by
  have hSC : ConductorExponent.SpectralConductorStatement.{u, uE} K :=
    SpectralConductor.spectralConductorRankOneReduction K
      (fun A => Ramification.Padic.finiteInertiaConductorRefinement K A)
      (SpectralConductor.commonClosureRankOneConductor p K)
  have hcont : (FiniteRepresentation.restrict (ConductorExponent.baseInclusion K).toMonoidHom
      A).IsContinuous :=
    FiniteRepresentation.isContinuous_restrict _
      (ConductorExponent.baseInclusion K).continuous_toFun hA
  obtain ⟨P⟩ := Ramification.HerbrandBridge.continuousWeilFiniteInertiaPresentation K _ hcont
  have hsurj := Ramification.HerbrandBridge.weilInertiaRestriction_surjective K P.extension
  have key := hSC e ε hε ψ μ A hA P hsurj
  set D : ℂ → ℂ := fun s => (conditionalDeligneValue K e ε hε (ConductorExponent.base K) ψ μ
    (ConductorExponent.baseClass K A hA) s : ℂ) with hD
  have hq := one_lt_baseCardinality K
  -- periodicity
  set t : ℂ := 2 * Real.pi * Complex.I / (Real.log (baseCardinality K) : ℂ) with ht
  have hpar : spectralParameter (baseCardinality K) (baseCardinality_pos K) t =
      spectralParameter (baseCardinality K) (baseCardinality_pos K) 0 := by
    apply Units.ext
    have hlog : (Real.log (baseCardinality K) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
    simp only [spectralParameter, Units.val_mk0, neg_zero, zero_mul, Complex.exp_zero]
    rw [ht, show -(2 * Real.pi * Complex.I / (Real.log (baseCardinality K) : ℂ)) *
        (Real.log (baseCardinality K) : ℂ) = -(2 * Real.pi * Complex.I) by field_simp,
      Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have hper : D t = D 0 := by
    simp only [hD, conditionalDeligneValue]
    rw [virtualTwist_eq_of_spectralParameter_eq K _ hpar]
  have hkt := key t
  change D t = D 0 * _ at hkt
  have hD0 : D 0 ≠ 0 := Units.ne_zero _
  rw [hper] at hkt
  have hone : (baseCardinality K : ℂ) ^
      (-(((P.artinConductor hsurj : ℚ) : ℂ) +
        (ConductorExponent.additiveConductor K ψ : ℂ) * (A.rank : ℂ)) * t) = 1 :=
    mul_left_cancel₀ hD0 (hkt.symm.trans (mul_one _).symm)
  obtain ⟨k, hk⟩ := exists_int_of_cpow_period hq hone
  refine ⟨k, fun s => ?_⟩
  have hks := key s
  change D s = D 0 * _ at hks
  change D s = D 0 * _
  rw [hks, hk, show -(k : ℂ) * s = (k : ℂ) * (-s) by ring, Complex.cpow_int_mul]
  congr 2

/-- The Weil–Deligne correction over the bottom field is its constant times
`(q^(-s))^d`, `d` the conductor correction. -/
theorem quotientValue_monomial (C : Pair.{u, uE} K (baseExtension K))
    (Φ : GeometricFrobenius K (baseExtension K)) (s : ℂ) :
    (quotientValue K (baseExtension K) C Φ s : ℂ) =
      (quotientValue K (baseExtension K) C Φ 0 : ℂ) *
        RankinSelberg.spectralPoint qK s ^
          ((WeilDeligne.conductorCorrection C (inertia K (baseExtension K)) : ℕ) : ℤ) := by
  have h : ∀ t : ℂ, (quotientValue K (baseExtension K) C Φ t : ℂ) =
      (WeilDeligne.quotientConstantCorrection C (inertia K (baseExtension K)) Φ.val : ℂ) *
        (spectralParameter (residueCardinality K (baseExtension K))
          (residueCardinality_pos K (baseExtension K)) t : ℂ) ^
          WeilDeligne.conductorCorrection C (inertia K (baseExtension K)) := fun t => by
    change ((WeilDeligne.quotientConstantCorrection C (inertia K (baseExtension K)) Φ.val *
      spectralParameter (residueCardinality K (baseExtension K))
          (residueCardinality_pos K (baseExtension K)) t ^
        WeilDeligne.conductorCorrection C (inertia K (baseExtension K)) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
  rw [h s, h 0, spectralParameter_zero, Units.val_one, one_pow, mul_one, zpow_natCast,
    spectralParameter_eq_cpow, baseResidueCardinality_real]
  simp [RankinSelberg.spectralPoint]

/-- The full conditional value of a continuous pair over the bottom field is its
value at `0` times an integral power of `q^(-s)`. -/
theorem conditionalEpsilonValue_monomial (e : ReciprocityFamily K)
    (ε : NonabelianSystem.Assignment.{u, uE} K) (hε : NonabelianSystem.IsSystem K e ε)
    (ψ : AdditiveCharacter K (baseExtension K)) (μ : HaarMeasure K (baseExtension K))
    (C : Pair.{u, uE} K (baseExtension K)) (hC : C.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius K (baseExtension K)) :
    ∃ m : ℤ, ∀ s : ℂ,
      (conditionalEpsilonValue K e ε hε (baseExtension K) ψ μ C hC Φ s : ℂ) =
        (conditionalEpsilonValue K e ε hε (baseExtension K) ψ μ C hC Φ 0 : ℂ) *
          RankinSelberg.spectralPoint qK s ^ m := by
  obtain ⟨k, hk⟩ := conditionalDeligneValue_monomial K e ε hε ψ μ C.toFiniteRepresentation hC
  have hk' : ∀ s : ℂ,
      (conditionalDeligneValue K e ε hε (baseExtension K) ψ μ
          (underlyingClass K (baseExtension K) C hC) s : ℂ) =
        (conditionalDeligneValue K e ε hε (baseExtension K) ψ μ
          (underlyingClass K (baseExtension K) C hC) 0 : ℂ) *
          RankinSelberg.spectralPoint qK s ^ k := hk
  refine ⟨k + (WeilDeligne.conductorCorrection C (inertia K (baseExtension K)) : ℤ),
    fun s => ?_⟩
  have hx : RankinSelberg.spectralPoint qK s ≠ 0 :=
    RankinSelberg.spectralPoint_ne_zero_of_pos
      (lt_trans Nat.zero_lt_one K.canonicalTopologicalData.residueCardinality_gt_one) s
  simp only [conditionalEpsilonValue, Units.val_mul]
  rw [hk' s, quotientValue_monomial K C Φ s, zpow_add₀ hx]
  ring

end ArithmeticPairEpsilonExistence

open ArithmeticPairEpsilonExistence in
/-- **Existence of arithmetic pair epsilon factors** for pairs of Weil–Deligne classes
with continuous representatives. -/
theorem arithmeticPairEpsilonExistence :
    ArithmeticPairEpsilonExistenceStatement.{u, uV, uE} := by
  intro p _ K eC ε hε ψ X Y ⟨B₁, hB₁, hB₁c⟩ ⟨B₂, hB₂, hB₂c⟩
  have hA₁ := basePair_isContinuous.{u, uV, uE} K hB₁c
  have hA₂ := basePair_isContinuous.{u, uV, uE} K hB₂c
  have hψ₀ : IsBaseCharacter K ψ (baseFieldAdditiveCharacterEquiv K ψ) :=
    (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv K ψ _).2 rfl
  have hμ₀ : IsSelfDual K (baseExtension K) (baseFieldAdditiveCharacterEquiv K ψ)
      (baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ)) :=
    (isSelfDual_baseFieldTransport_iff K ψ _).2 (isSelfDual_localSelfDualHaar K ψ)
  obtain ⟨m, hm⟩ := conditionalEpsilonValue_monomial K eC ε hε
    (baseFieldAdditiveCharacterEquiv K ψ) (baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ))
    (WeilDeligneRepresentation.tensor (basePair.{u, uV, uE} K B₁) (basePair.{u, uV, uE} K B₂))
    (CommonClosureGamma.tensor_isContinuous K _ _ _ hA₁ hA₂) (baseGeometricFrobenius K)
  refine ⟨CommonClosureGamma.conditionalPairEpsilonValue K eC ε hε (baseExtension K)
      (baseFieldAdditiveCharacterEquiv K ψ) (baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ))
      (basePair.{u, uV, uE} K B₁) (basePair.{u, uV, uE} K B₂) hA₁ hA₂
      (baseGeometricFrobenius K) 0, m,
    ⟨baseFieldAdditiveCharacterEquiv K ψ, baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ),
      basePair.{u, uV, uE} K B₁, basePair.{u, uV, uE} K B₂,
      ⟨hψ₀, hμ₀, hB₁ ▸ basePair_isBaseRestriction K B₁,
        hB₂ ▸ basePair_isBaseRestriction K B₂⟩, hA₁, hA₂⟩,
    ⟨baseGeometricFrobenius K⟩, ?_⟩
  rintro ψ' μ A B ⟨hψ', hμ, hA, hB⟩ hAc hBc Φ s
  obtain rfl : ψ' = baseFieldAdditiveCharacterEquiv K ψ :=
    (isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv K ψ ψ').1 hψ'
  obtain rfl : μ = baseFieldHaarMeasureEquiv K (localSelfDualHaar K ψ) := by
    have h := eq_localSelfDualHaar K ψ _
      ((isSelfDual_of_isBaseCharacter_iff K ψ _ hψ' μ).1 hμ)
    rw [← h, Equiv.apply_symm_apply]
  obtain ⟨f⟩ := IsBaseRestriction.nonempty_equiv K hB₁ hA
  obtain ⟨g⟩ := IsBaseRestriction.nonempty_equiv K hB₂ hB
  rw [CommonClosureGamma.conditionalPairEpsilonValue_eq_of_equiv K eC ε hε _ _ _ hAc hA₁ hBc hA₂
    (f.symm.trans (basePairEquiv K B₁)) (g.symm.trans (basePairEquiv K B₂)) Φ s]
  unfold CommonClosureGamma.conditionalPairEpsilonValue
  rw [conditionalEpsilonValue_eq_of_frobenius K eC ε hε _ _ _ _ _ (baseGeometricFrobenius K) Φ s,
    hm s]
  rfl

end Langlands.Correspondence
