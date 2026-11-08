import Langlands.Representation.RankinSelberg.UniformRankOneTwistLVanishing
import Langlands.Representation.RankinSelberg.UniformRankOneTwistEpsilon
import Langlands.Representation.RankinSelberg.UniformRankOneTwistStatement
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonProof
import Langlands.Representation.RankinSelberg.PadicGenericGammaExpression
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Whittaker.FunctionalExistence
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction
import Langlands.Correspondence.SegmentEpsilonAlgebra
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedTwistIntegrability

/-!
# Level-uniform rank-one stability under highly ramified twists: assembly
-/

noncomputable section

namespace Langlands.RankinSelberg.UniformRankOneTwist

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniformTwistProofTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance uniformTwistProofValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance uniformTwistProofLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance uniformTwistProofT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance uniformTwistProofMeasurable : MeasurableSpace F.Carrier := borel _
local instance uniformTwistProofBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance uniformTwistProofGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance uniformTwistProofGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The trivial character of `GL_1` is generic. -/
theorem isGeneric_rankOneCharacter_one (ψ : UnitaryAdditiveCharacter F.Carrier) :
    Whittaker.IsGeneric ψ 0 (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) := by
  have hirr : Representation.IsIrreducible (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) :=
    Classification.isIrreducible_of_linearEquiv_complex _ (LinearEquiv.refl ℂ ℂ)
  exact Whittaker.isGeneric_rankOne ψ _ (rankOneCharacter_isOfWhittakerType p F ψ 1).1

/-- A determinant twist of a generic representation by a quasicharacter is generic. -/
theorem isGeneric_twist (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ r π) (χ : Quasicharacter F.Carrier) :
    Whittaker.IsGeneric ψ r (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) := by
  have hT : IsOfWhittakerType r (standardCharacter ψ r)
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) :=
    (isOfWhittakerType_quasicharacter_twist_iff F.canonicalTopologicalData ψ χ π).mpr
      (isOfWhittakerType_of_isGeneric F hπ)
  refine ⟨(isIrreducible_twist_iff _ π).mpr hπ.1, hT.1, ?_⟩
  obtain ⟨e⟩ := hT.2.2
  refine ⟨e.symm 1, fun h => ?_⟩
  have h0 : e.symm 1 = 0 := Subtype.ext h
  have h1 : e (e.symm 1) = 1 := e.apply_symm_apply 1
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

/-- A principal-level fixed vector is an eigenvector of the twist at every
smaller principal level. -/
theorem twist_apply_of_mem_fixedVectors
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : F.Carrierˣ →* ℂˣ) {m m' : ℕ} (hm : m ≤ m') {w : V}
    (hw : w ∈ Langlands.fixedVectors π (Conductor.principalLevelSubgroup F.Carrier r m))
    {k : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ Conductor.principalLevelSubgroup F.Carrier r m') :
    Langlands.twist (χ.comp determinant) π k w =
      ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w := by
  have hk' : k ∈ Conductor.principalLevelSubgroup F.Carrier r m :=
    Conductor.principalLevelSubgroup_antitone F.Carrier r hm hk
  have hfix : π k w = w := hw ⟨k, hk'⟩
  change ((χ.comp determinant k : ℂˣ) : ℂ) • π k w = _
  rw [hfix]
  rfl

/-- **The coefficient-model package of a ramified twist.** For `π` generic with a
nonzero principal level-`m` fixed vector and `χ` of conductor exceeding `max m 1`, the
coefficient model of `σ = π ⊗ χ ∘ det` for a nonzero standard functional carries
Godement–Jacquet data with both polynomials `1` and a nonzero `χ ∘ det`-eigenvector
for the level `max m 1`; moreover `L(s, σ × 1) = 1`, the gamma factor of `σ × 1`
is the matrix monomial, and the epsilon factor of `σ × 1` is `(c, a)`. -/
theorem twistedModel_package (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπ : Whittaker.IsGeneric ψ r π) {m : ℕ} (hlev : HasPrincipalLevelVector F π m)
    (χ : Quasicharacter F.Carrier)
    (hχ : max m 1 < F.canonicalTopologicalData.multiplicativeConductor χ) :
    ∃ (ℓ : glFunctionals ψ r (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π))
      (_ : ℓ.val ≠ 0) (c : ℂˣ) (a : ℤ)
      (w : (glCoefficientModel ψ r
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule),
      IsOfWhittakerType (V := (glCoefficientModel ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule) r
        (standardCharacter ψ r) (glModelRepresentation ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ) ∧
      Representation.IsIrreducible (V := (glCoefficientModel ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (glModelRepresentation ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ) ∧
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν.val
        (V := (glCoefficientModel ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
        (glModelRepresentation ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ) 1 1 c a ∧
      w ≠ 0 ∧
      (∀ k ∈ Conductor.principalLevelSubgroup F.Carrier r (max m 1),
        glModelRepresentation ψ r
          (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ k w =
          ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w) ∧
      IsPadicSymmetricLPolynomial F ψ ν.val
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 ∧
      IsPadicSymmetricGammaFactor F ψ ν.val
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
        (rationalGammaExpression (LocalFactor.residueReflection F) c a 1 1) ∧
      IsPadicSymmetricEpsilonFactor F ψ ν.val
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
        (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) (c, a) := by
  set σ := Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π with hσdef
  have hσgen : Whittaker.IsGeneric ψ r σ := isGeneric_twist F ψ π hπ χ
  have hσ : IsOfWhittakerType r (standardCharacter ψ r) σ := isOfWhittakerType_of_isGeneric F hσgen
  obtain ⟨w0, hw0mem, hw0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hlev
  have hw0 : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier r (max m 1),
      σ k w0 = ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w0 :=
    fun k hk => twist_apply_of_mem_fixedVectors F π χ (le_max_left m 1) hw0mem hk
  obtain ⟨u, hu, hχu⟩ : ∃ u ∈ F.canonicalTopologicalData.principalUnits (max m 1), χ u ≠ 1 := by
    by_contra h
    push Not at h
    have htriv : F.canonicalTopologicalData.MultiplicativeTrivialAt χ (max m 1) := h
    rw [F.canonicalTopologicalData.multiplicativeTrivialAt_iff_conductor_le] at htriv
    omega
  obtain ⟨e₀⟩ := hσ.2.2
  let ℓ : glFunctionals ψ r σ := e₀.symm 1
  have hℓ : ℓ.val ≠ 0 := by
    intro h
    have h0 : ℓ = 0 := Subtype.ext h
    have h1 : e₀ ℓ = 1 := e₀.apply_symm_apply 1
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  let : Representation.IsIrreducible σ := hσgen.1
  let e := Whittaker.modelEquiv σ ℓ hℓ
  have hρirr : Representation.IsIrreducible (glModelRepresentation ψ r σ ℓ) :=
    (isIrreducible_iff_of_equiv (W := (glCoefficientModel ψ r σ ℓ).toSubmodule) e).mp hσgen.1
  have hρ : IsOfWhittakerType (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) r
      (standardCharacter ψ r) (glModelRepresentation ψ r σ ℓ) :=
    hσ.of_equiv e
  obtain ⟨P, PDual, c, a, hdata⟩ := GodementJacquet.genericMatrixFunctionalEquation.{uF, uF} p F
    ψ ν.val ν.2 r (glCoefficientModel ψ r σ ℓ).toSubmodule (glModelRepresentation ψ r σ ℓ)
    hρ hρirr
  have hew0 : Whittaker.modelMap σ ℓ w0 ≠ 0 := by
    intro h
    apply hw0ne
    have h' : e w0 = e 0 := by
      rw [map_zero]
      exact h
    exact EquivLike.injective e h'
  have hew : ∀ k ∈ Conductor.principalLevelSubgroup F.Carrier r (max m 1),
      glModelRepresentation ψ r σ ℓ k (Whittaker.modelMap σ ℓ w0) =
        ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • Whittaker.modelMap σ ℓ w0 := by
    intro k hk
    change Whittaker.modelRepresentation σ ℓ k (Whittaker.modelMap σ ℓ w0) = _
    rw [← (Whittaker.modelMap σ ℓ).isIntertwining, hw0 k hk, map_smul]
  obtain ⟨hP1, hPD1⟩ := eq_one_of_normalizedMatrixFunctionalEquationData F ψ ν.val _ hρ.1.1 hρirr
    (χ : F.Carrierˣ →* ℂˣ) (lt_of_lt_of_le zero_lt_one (le_max_right m 1)) u hu hχu hew0 hew hdata
  subst hP1 hPD1
  obtain ⟨P', hP', hgen'⟩ :=
    GodementJacquet.Padic.exists_modelMatrixNormalizedGenerator F ψ σ ν hσ
  have hL : IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 := by
    have hPP : P' = 1 := (hgen' ℓ hℓ).unique hdata.1.2.2
    rw [hPP] at hP'
    exact hP'
  have hG := rankOneMatrixFunctionalEquationComparison.{uF, uV} p F ψ ν.val ν.2 r V σ hσ ℓ hℓ
    1 1 c a hdata
  have h1gen := isGeneric_rankOneCharacter_one F ψ
  have hGeq := genericSymmetricGammaFactor_eq F ψ ν.val ν.2 σ
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hσgen h1gen hG
  have hexp := genericSymmetricGammaFactor_eq_expression F ψ ν.val ν.2 σ
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hσgen h1gen
  have hLeq := genericSymmetricLPolynomial_eq F ψ ν.val σ
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hσgen h1gen hL
  have hGeq2 := hexp.symm.trans hGeq
  rw [hLeq] at hGeq2
  obtain ⟨hc, ha⟩ := rationalGammaExpression_cancel one_ne_zero
    (genericSymmetricDualLPolynomial_coeff_zero F ψ ν.val σ _ hσgen h1gen)
    Polynomial.coeff_one_zero hGeq2
  have hε := genericSymmetricEpsilonData_isPadic F ψ ν.val ν.2 σ
    (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hσgen h1gen
  have hεeq : genericSymmetricEpsilonData F ψ ν.val ν.2 σ
      (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hσgen h1gen = (c, a) := Prod.ext hc ha
  rw [hεeq] at hε
  exact ⟨ℓ, hℓ, c, a, Whittaker.modelMap σ ℓ w0, hρ, hρirr, hdata, hew0, hew, hL, hG, hε⟩

/-- The coefficient model of a determinant twist `σ = π ⊗ χ ∘ det` has central
character `ω · χ^(r+1)` when `π` has central character `ω`. -/
theorem model_hasGLCentralCharacter (ψ : UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (ω : F.Carrierˣ →* ℂˣ)
    (hω : Classification.HasGLCentralCharacter F.Carrier (r + 1) π ω)
    (ℓ : glFunctionals ψ r (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)) :
    Classification.HasGLCentralCharacter F.Carrier (r + 1)
      (V := (glCoefficientModel ψ r
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ).toSubmodule)
      (glModelRepresentation ψ r
        (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π) ℓ)
      (ω * (χ : F.Carrierˣ →* ℂˣ) ^ (r + 1)) := by
  intro z f
  obtain ⟨v, rfl⟩ := Whittaker.modelMap_surjective _ ℓ f
  change Whittaker.modelRepresentation _ ℓ _ (Whittaker.modelMap _ ℓ v) = _
  rw [← (Whittaker.modelMap _ ℓ).isIntertwining]
  have hσz : Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) z) v =
      (((ω * (χ : F.Carrierˣ →* ℂˣ) ^ (r + 1)) z : ℂˣ) : ℂ) • v := by
    change ((((χ : F.Carrierˣ →* ℂˣ).comp determinant
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) z)) : ℂˣ) : ℂ) •
        π (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) z) v = _
    rw [hω z v, smul_smul]
    simp only [MonoidHom.comp_apply, determinant, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, map_pow, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val]
    ring_nf
  rw [hσz, map_smul]

/-- Schur's lemma for the scalar matrices: an irreducible admissible representation
of `GL_(r+1)(F)` has a central character. -/
theorem exists_hasGLCentralCharacter
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hπa : IsAdmissible π) (hπi : Representation.IsIrreducible π) :
    ∃ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (r + 1) π ω := by
  let A := (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (R := F.Carrier)).range
  have hA : A ≤ Subgroup.center (Langlands.GeneralLinear (r + 1) F.Carrier) := by
    rintro _ ⟨z, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Matrix.GeneralLinearGroup.scalar_commute z g).symm
  obtain ⟨c, hc⟩ := HarishChandraSchwartz.exists_centralCharacter_of_isIrreducible A hA hπa hπi
  refine ⟨c.comp (Matrix.GeneralLinearGroup.scalar (Fin (r + 1))).rangeRestrict, fun z v => ?_⟩
  exact hc ((Matrix.GeneralLinearGroup.scalar (Fin (r + 1))).rangeRestrict z) v

section Assembly

/-- The assembly of the level-uniform statement for one field, one additive character
and one self-dual measure, from the explicit test-function computation `hB` of the
exponent and the constant of the matrix functional equation of a ramified twist. -/
theorem uniformRankOneTwist_of_core (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) (r m : ℕ)
    (const : Quasicharacter F.Carrier → (F.Carrierˣ →* ℂˣ) → ℂ)
    (hB : ∀ {W : Type uF} [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W),
      IsOfWhittakerType r (standardCharacter ψ r) ρ → Representation.IsIrreducible ρ →
      ∀ ω : F.Carrierˣ →* ℂˣ, Classification.HasGLCentralCharacter F.Carrier (r + 1) ρ ω →
      ∀ χ : Quasicharacter F.Carrier,
        2 * max m 1 ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ w : W, w ≠ 0 →
      (∀ k ∈ Conductor.principalLevelSubgroup F.Carrier r (max m 1),
        ρ k w = ((χ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ) • w) →
      ∀ (c : ℂˣ) (a : ℤ), GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν.val ρ
        1 1 c a →
      a = (((r + 1) * F.canonicalTopologicalData.multiplicativeConductor χ : ℕ) : ℤ) ∧
        (c : ℂ) = const χ ω) :
    ∃ B : ℕ,
      (∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V),
        Whittaker.IsGeneric ψ r π →
        HasPrincipalLevelVector F π m →
        ∀ χ : Quasicharacter F.Carrier,
          B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          IsPadicSymmetricLPolynomial F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) 1 ∧
            ∃ c : ℂˣ, IsPadicSymmetricEpsilonFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
              (c, (((r + 1) * F.canonicalTopologicalData.multiplicativeConductor χ : ℕ) : ℤ))) ∧
      (∀ {V₁ V₂ : Type uV} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
        (π₁ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₁)
        (π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂),
        Whittaker.IsGeneric ψ r π₁ → Whittaker.IsGeneric ψ r π₂ →
        HasPrincipalLevelVector F π₁ m → HasPrincipalLevelVector F π₂ m →
        SameGLCentralCharacter F π₁ π₂ →
        ∀ χ : Quasicharacter F.Carrier,
          B ≤ F.canonicalTopologicalData.multiplicativeConductor χ →
          ∃ G : RationalFunctions,
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G ∧
            IsPadicSymmetricGammaFactor F ψ ν.val
              (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂)
              (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) G) := by
  refine ⟨2 * max m 1 + 1, ?_, ?_⟩
  · intro V _ _ π hπ hlev χ hχB
    have hχ : max m 1 < F.canonicalTopologicalData.multiplicativeConductor χ := by omega
    obtain ⟨ℓ, hℓ, c, a, w, hρ, hρirr, hdata, hw0, hw, hL, -, hε⟩ :=
      twistedModel_package F ψ ν π hπ hlev χ hχ
    obtain ⟨ω, hω⟩ := exists_hasGLCentralCharacter F π hπ.2.1 hπ.1
    obtain ⟨ha, -⟩ := hB _ hρ hρirr _ (model_hasGLCentralCharacter F ψ π χ ω hω ℓ) χ (by omega)
      w hw0 hw c a hdata
    rw [ha] at hε
    exact ⟨hL, c, hε⟩
  · intro V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ hlev₁ hlev₂ hsame χ hχB
    obtain ⟨ω, hω₁, hω₂⟩ := hsame
    have hχ : max m 1 < F.canonicalTopologicalData.multiplicativeConductor χ := by omega
    obtain ⟨ℓ₁, hℓ₁, c₁, a₁, w₁, hρ₁, hρirr₁, hdata₁, hw0₁, hw₁, -, hG₁, -⟩ :=
      twistedModel_package F ψ ν π₁ hπ₁ hlev₁ χ hχ
    obtain ⟨ℓ₂, hℓ₂, c₂, a₂, w₂, hρ₂, hρirr₂, hdata₂, hw0₂, hw₂, -, hG₂, -⟩ :=
      twistedModel_package F ψ ν π₂ hπ₂ hlev₂ χ hχ
    obtain ⟨ha₁, hc₁⟩ := hB _ hρ₁ hρirr₁ _ (model_hasGLCentralCharacter F ψ π₁ χ ω hω₁ ℓ₁) χ
      (by omega) w₁ hw0₁ hw₁ c₁ a₁ hdata₁
    obtain ⟨ha₂, hc₂⟩ := hB _ hρ₂ hρirr₂ _ (model_hasGLCentralCharacter F ψ π₂ χ ω hω₂ ℓ₂) χ
      (by omega) w₂ hw0₂ hw₂ c₂ a₂ hdata₂
    have hc : c₁ = c₂ := Units.ext (hc₁.trans hc₂.symm)
    have ha : a₁ = a₂ := ha₁.trans ha₂.symm
    subst hc ha
    exact ⟨_, hG₁, hG₂⟩

/-- **Jacquet–Shalika 1985, Proposition (2.2), level-uniform form.** -/
theorem uniformRankOneTwist : UniformRankOneTwistStatement.{uF, uV} := by
  intro p _ F ψ ν hψ r m
  refine uniformRankOneTwist_of_core F ψ ν r m
    (fun χ ω => twistedMatrixEpsilonConstant F ψ ν.val r χ ω) ?_
  intro W _ _ ρ hρ _ ω hω χ hχ w hw hwχ c a hdata
  exact twistedMatrixEpsilon F ψ hψ ν.val ρ hρ.1.1 ω hω χ (le_max_right m 1) hχ hw hwχ hdata

end Assembly

end Langlands.RankinSelberg.UniformRankOneTwist
