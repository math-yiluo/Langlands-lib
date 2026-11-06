import Langlands.Representation.RankinSelberg.SupercuspidalTwistParameters
import Langlands.Representation.Unitary.CentralCharacterProof

/-! # Unitary contragredient twist parameters -/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW uG

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A nonzero twisted bilinear form between representations with unitary
central characters forces its twisting character to have norm one on the center. -/
theorem norm_character_eq_one_of_twisted_bilinear
    (cπ : UnitaryCentralCharacter π) (cσ : UnitaryCentralCharacter σ)
    (χ : G →* ℂˣ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : β ≠ 0)
    (hcov : ∀ g v w, β (π g v) (σ g w) = (χ g : ℂ)⁻¹ * β v w)
    (z : Subgroup.center G) :
    ‖(χ z : ℂ)‖ = 1 := by
  classical
  obtain ⟨v, w, hvw⟩ : ∃ v w, β v w ≠ 0 := by
    by_contra h
    push Not at h
    apply hβ
    ext v w
    exact h v w
  have hcovz := hcov z v w
  simp only [cπ.acts, cσ.acts, map_smul, LinearMap.smul_apply, smul_eq_mul] at hcovz
  have hscalar : (cπ.character z : ℂ) * (cσ.character z : ℂ) =
      (χ z : ℂ)⁻¹ := by
    apply mul_right_cancel₀ hvw
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcovz
  have hn := congrArg norm hscalar
  simp only [norm_mul, cπ.norm_eq_one, cσ.norm_eq_one, one_mul, norm_inv] at hn
  exact inv_eq_one.mp hn.symm

end Pairing

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)

/-- Every contragredient unramified-twist parameter of two irreducible,
admissible, unitarizable representations has complex norm one. -/
theorem IsContragredientTwistParameter.norm_eq_one {a : ℂ}
    (ha : IsContragredientTwistParameter F π σ a)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    (hπu : IsUnitarizable π) (hσu : IsUnitarizable σ) :
    ‖a‖ = 1 := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  obtain ⟨cπ⟩ := unitarizableCentralCharacter π hπa hπ hπu
  obtain ⟨cσ⟩ := unitarizableCentralCharacter σ hσa hσ hσu
  obtain ⟨u, rfl, χ, hχ, ⟨e⟩⟩ := ha
  obtain ⟨β, hβ, hcov⟩ := exists_twisted_bilinear_of_contragredient_equiv
    π σ (χ.comp determinant) hπ e
  let z : Subgroup.center (Langlands.GeneralLinear (r + 1) F.Carrier) :=
    ⟨centralSpectralElement T (r + 1), centralSpectralElement_mem_center T (r + 1)⟩
  have hn := norm_character_eq_one_of_twisted_bilinear cπ cσ
    (χ.comp determinant) β hβ hcov z
  have hvalue : ((χ.comp determinant)
      (z : Langlands.GeneralLinear (r + 1) F.Carrier) : ℂ) =
      ((T.residueCardinality : ℂ) ^ (-u)) ^ (r + 1) := by
    rw [MonoidHom.comp_apply, hχ]
    change determinantWeight (normalizedAbsoluteValue T)
      (centralSpectralElement T (r + 1)) (-u) =
      ((T.residueCardinality : ℂ) ^ (-u)) ^ (r + 1)
    simpa only [neg_neg, spectralPoint] using
      determinantWeight_centralSpectralElement T (r + 1) u
  rw [hvalue, norm_pow] at hn
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero r)).mp hn

/-- The exact finite contragredient-twist set, together with its unit-circle
support for the supplied representations. -/
structure UnitaryContragredientTwistParameterSet where
  parameters : Finset ℂ
  mem_iff : ∀ a, a ∈ parameters ↔ IsContragredientTwistParameter F π σ a
  norm_eq_one : ∀ a ∈ parameters, ‖a‖ = 1

/-- Construct the finite unit-circle parameter set from actual irreducible,
admissible, unitarizable inputs. -/
def unitaryContragredientTwistParameterSet
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ)
    (hπu : IsUnitarizable π) (hσu : IsUnitarizable σ) :
    UnitaryContragredientTwistParameterSet F π σ := by
  classical
  let h := exists_finset_contragredientTwistParameters F π σ hπ hσ hπa hσa
  let A := Classical.choose h
  have hA := Classical.choose_spec h
  exact ⟨A, hA, fun a ha =>
    IsContragredientTwistParameter.norm_eq_one F π σ
      ((hA a).mp ha) hπ hσ hπa hσa hπu hσu⟩

end Langlands.RankinSelberg
