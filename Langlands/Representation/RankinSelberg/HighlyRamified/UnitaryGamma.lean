import Langlands.Representation.RankinSelberg.HighlyRamified.RankOneMonomial
import Langlands.Representation.RankinSelberg.HighlyRamified.MonomialGamma
import Langlands.Representation.RankinSelberg.HighlyRamifiedGammaAssembly
import Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof
import Langlands.Representation.Unramified.PrincipalSeries

/-!
# Gamma factors of a highly ramified twist against unramified principal series

Let `τ` be generic of rank `n + 3` and `η` of large conductor, and put `e = (n + 3) a(η)`.
By the uniform rank-one statement every gamma factor of `(τ ⊗ η ∘ det, 1)` is `c X^e`.
Twisting the trivial test by the unramified character with value `z` at the uniformizer
rescales this factor to `c z^e X^e` (`unramifiedTwistGamma`), and gamma multiplicativity
gives, for the normalized principal series `I(z)` of rank `n + 2`, the gamma factor
`c^(n+2) (∏ z_i)^e X^(e (n+2))`. The constant `c` does not depend on `z`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-- Every nonzero complex number is a spectral point `q^(-u)`. -/
theorem exists_spectralShiftUnit_eq {q : ℕ} (hq : 1 < q) (z : ℂˣ) :
    ∃ u : ℂ, spectralShiftUnit q hq u = z := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q)]
  have hlogq : (Real.log q : ℂ) ≠ 0 := by
    have : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
    exact_mod_cast this.ne'
  refine ⟨-(Complex.log z) / (Real.log q : ℂ), Units.ext ?_⟩
  rw [coe_spectralShiftUnit, spectralPoint, Complex.cpow_def_of_ne_zero hq0, hlog]
  have h : (Real.log q : ℂ) * -(-Complex.log z / (Real.log q : ℂ)) = Complex.log z := by
    field_simp
  rw [h, Complex.exp_log (Units.ne_zero z)]

/-- A finite product of epsilon monomials is an epsilon monomial. -/
theorem prod_rationalEpsilonMonomial_coe {ι : Type*} (s : Finset ι) (c : ι → ℂˣ) (e : ι → ℤ) :
    ∏ i ∈ s, (rationalEpsilonMonomial (c i) (e i) : RationalFunctions) =
      rationalEpsilonMonomial (∏ i ∈ s, c i) (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      rationalEpsilonMonomial_mul_coe]

/-- Twisting the trivial rank-one test by `χ ∘ det` gives the rank-one test `χ`. -/
theorem twist_rankOneCharacter_one {F : Type*} [Field F] (χ : Fˣ →* ℂˣ) :
    Langlands.twist (χ.comp determinant) (rankOneCharacter (1 : Fˣ →* ℂˣ)) =
      rankOneCharacter χ := by
  ext g
  simp [Langlands.twist, Langlands.characterRepresentation]

section Canonical

variable (F : PadicField.{uF} p)

/-- The rescaling of a gamma factor by an unramified twist `|·|^u` of the trivial test, with
`q^(-u) = z`: every gamma factor `c X^e` of `(π, 1)` gives the gamma factor `c z^e X^e` of
`(π, μ_z)`, where `μ_z` is the unramified character with `μ_z(ϖ) = z`. -/
theorem isPadicSymmetricGammaFactor_unramifiedTest
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (c : ℂˣ) (e : ℤ)
    (hG : IsPadicSymmetricGammaFactor F ψ ν.val π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
      (rationalEpsilonMonomial c e))
    (z : ℂˣ) :
    IsPadicSymmetricGammaFactor F ψ ν.val π
      (rankOneCharacter (F.canonicalTopologicalData.unramifiedCharacter z))
      (rationalEpsilonMonomial (c * z ^ e) e) := by
  let T := F.canonicalTopologicalData
  obtain ⟨u, hu⟩ := exists_spectralShiftUnit_eq T.residueCardinality_gt_one z
  let χ := T.unramifiedCharacter
    (LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos u)
  have hχ : ∀ x : F.Carrierˣ,
      (χ x : ℂ) = (T.normalizedAbs (x : F.Carrier) : ℂ) ^ u := by
    intro x
    simpa only [T.determinantNorm_scalar, pow_one, T.normalizedAbsUnits_coe,
      PadicField.TopologicalData.determinantComplexPower,
      PadicField.TopologicalData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
      GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using
      T.determinantComplexPower_apply 1 u (GeneralLinear.scalar x)
  have hpar : LocalFactor.spectralParameter T.residueCardinality T.residueCardinality_real_pos u
      = z := by
    rw [← hu]
    apply Units.ext
    rw [LocalFactor.spectralParameter_eq_cpow, coe_spectralShiftUnit, spectralPoint,
      Complex.ofReal_natCast]
  have hχz : χ = T.unramifiedCharacter z := by
    simp only [χ, hpar]
  have h := (unramifiedTwistGamma p F ψ ν r 0 π (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) u χ hχ
    _ hG).1
  rw [twist_rankOneCharacter_one, hχz, hu] at h
  convert h using 1
  simp only [coe_rationalEpsilonMonomial, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul,
    map_zpow₀, rationalRescale_C, rationalRescale_X, RatFunc.algebraMap_eq_C]
  rw [mul_zpow, ← map_zpow₀ RatFunc.C]
  ring

/-- Gamma factors of highly ramified twists against unramified principal series. For each
level `f` there is `B` such that for every generic `τ` of rank `n + 3` with a level-`f` vector
and every `η` with `a(η) ≥ B` there is `c` with the following property: for every `z`, with
`e = (n + 3) a(η)`, the factor `c^(n+2) (∏ z_i)^e X^((n+2) e)` is a gamma factor of
`(τ ⊗ η ∘ det, I(z))`, where `I(z)` is the normalized principal series of the unramified
characters with uniformizer values `z_i`. -/
theorem exists_bound_principalSeriesGamma (h3 : UniformRankOneTwistStatement.{uF, uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0) (n f : ℕ) :
    ∃ B : ℕ, ∀ {X : Type uV} [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 2 + 1) F.Carrier) X),
      (letI := F.canonicalTopologicalData.topology; Whittaker.IsGeneric ψ (n + 2) τ) →
      HasPrincipalLevelVector F τ f →
      ∀ η : (letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
        B ≤ F.canonicalTopologicalData.multiplicativeConductor η →
        ∃ c : ℂˣ, ∀ z : Fin (n + 1 + 1) → ℂˣ,
          IsPadicSymmetricGammaFactor F ψ ν.val
            (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
            (Unramified.principalSeriesOfTuple F z)
            (rationalEpsilonMonomial (c ^ (n + 2) * (∏ i, z i) ^
                (((n + 2 + 1) * F.canonicalTopologicalData.multiplicativeConductor η : ℕ) : ℤ))
              (((n + 2 : ℕ) : ℤ) *
                (((n + 2 + 1) * F.canonicalTopologicalData.multiplicativeConductor η : ℕ) : ℤ))) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨B, hB⟩ := exists_bound_rankOne_gammaMonomial h3 F ψ ν hψ (n + 2) f
  refine ⟨B, ?_⟩
  intro X _ _ τ hτ hf η hη
  set e : ℤ := (((n + 2 + 1) * T.multiplicativeConductor η : ℕ) : ℤ) with he
  have hW : IsOfWhittakerType (n + 2) (standardCharacter ψ (n + 2))
      (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ) :=
    isOfWhittakerType_of_isGeneric F (isGeneric_quasicharacter_twist T ψ η hτ)
  have h1 : ∑ _i : Fin 1, (0 + 1) = 0 + 1 := by simp
  obtain ⟨G₁, hG₁, -⟩ := gammaMultiplicativity p F ψ ν (n + 2) 0 1 (fun _ => 0) h1
    (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
    (fun _ => rankOneCharacter (1 : F.Carrierˣ →* ℂˣ)) hW
    (fun _ => rankOneCharacter_isOfWhittakerType p F ψ 1)
  obtain ⟨c, hc⟩ := hB τ hτ hf η hη (G₁ 0) (hG₁ 0)
  refine ⟨c, fun z => ?_⟩
  have hG₁' := hG₁ 0
  rw [hc] at hG₁'
  have hblock : ∀ i, IsPadicSymmetricGammaFactor F ψ ν.val
      (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter (T.unramifiedCharacter (z i))) (rationalEpsilonMonomial (c * z i ^ e) e) :=
    fun i => isPadicSymmetricGammaFactor_unramifiedTest F ψ ν _ c e hG₁' (z i)
  have hs : ∑ _i : Fin (n + 1 + 1), (0 + 1) = n + 1 + 1 := by simp
  obtain ⟨G, hG, hGP⟩ := gammaMultiplicativity p F ψ ν (n + 2) (n + 1) (n + 1 + 1)
    (fun _ => 0) hs (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
    (fun i => rankOneCharacter (T.unramifiedCharacter (z i))) hW
    (fun i => rankOneCharacter_isOfWhittakerType p F ψ (Unramified.character F (z i)))
  have hGi : ∀ i, G i = rationalEpsilonMonomial (c * z i ^ e) e :=
    fun i => (hG i).unique (hblock i)
  have hP : IsPadicSymmetricGammaFactor F ψ ν.val
      (Langlands.twist ((η : F.Carrierˣ →* ℂˣ).comp determinant) τ)
      (Unramified.principalSeriesOfTuple F z) (∏ i, G i) := hGP
  rw [Finset.prod_congr rfl (fun i _ => hGi i), prod_rationalEpsilonMonomial_coe] at hP
  convert hP using 3
  · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_zpow]
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Canonical

end Langlands.RankinSelberg.HighlyRamified
