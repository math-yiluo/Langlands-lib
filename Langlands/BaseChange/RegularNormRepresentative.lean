import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.Group.GL.UpperBruhatCoordinatesProof

/-! # Continuous ordinary representatives of regular twisted norms -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands Matrix _root_.Polynomial
open SigmaLiftCharacterIdentity (coefficients coefficients_associated coefficients_baseChange
  charpoly_eq_of_baseChange_coefficients continuous_charpoly_coefficient continuous_cyclicNorm)

private theorem charpolyActionMatrix_entry {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    charpolyActionMatrix n A.charpoly i j =
      if (j : ℕ) + 1 < n then ((X : F[X]) ^ ((j : ℕ) + 1)).coeff i
      else - A.charpoly.coeff i := by
  change (((X : F[X]) ^ ((j : ℕ) + 1)) %ₘ A.charpoly).coeff i = _
  have hd : A.charpoly.degree = n := by rw [charpoly_degree_eq_dim, Fintype.card_fin]
  by_cases hj : (j : ℕ) + 1 < n
  · rw [ite_eq_left hj, (modByMonic_eq_self_iff A.charpoly_monic).mpr]
    simpa only [degree_X_pow, hd, Nat.cast_lt] using hj
  · have hlast : (j : ℕ) + 1 = n := by
      have := j.isLt
      omega
    have hdeg : ((X : F[X]) ^ n).degree = A.charpoly.degree := by rw [degree_X_pow, hd]
    have hlead : ((X : F[X]) ^ n).leadingCoeff = A.charpoly.leadingCoeff := by
      rw [(monic_X_pow n).leadingCoeff, A.charpoly_monic.leadingCoeff]
    have hs := degree_sub_lt_right hdeg A.charpoly_monic.ne_zero hlead
    have hmod : (X ^ n : F[X]) %ₘ A.charpoly = X ^ n - A.charpoly := calc
      _ = (X ^ n - A.charpoly + A.charpoly) %ₘ A.charpoly := by rw [sub_add_cancel]
      _ = (X ^ n - A.charpoly) %ₘ A.charpoly := by
        rw [add_modByMonic, modByMonic_self A.charpoly_monic, add_zero]
      _ = _ := (modByMonic_eq_self_iff A.charpoly_monic).mpr hs
    rw [ite_eq_right hj, hlast, hmod, coeff_sub, coeff_X_pow, ite_eq_right (Nat.ne_of_lt i.isLt),
      zero_sub]

private theorem val_cyclicBasis_conjugate {F : Type*} [Field F] {n : ℕ}
    (γ B : GeneralLinear n F) (v : Fin n → F)
    (hB : B.val = cyclicBasisMatrix γ.val v) :
    (B⁻¹ * γ * B).val = charpolyActionMatrix n γ.val.charpoly := by
  have hmul := mul_cyclicBasisMatrix γ.val v
  rw [← hB] at hmul
  calc
    (B⁻¹ * γ * B).val = (B⁻¹).val * (γ.val * B.val) := by
      simp only [Units.val_mul, mul_assoc]
    _ = ((B⁻¹).val * B.val) * charpolyActionMatrix n γ.val.charpoly := by rw [hmul, mul_assoc]
    _ = _ := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

universe u v

/-- The regular twisted norm admits continuous associated ordinary
representatives through any prescribed associated regular pair. -/
def RegularNormRepresentativeStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ), IsCyclicAlgebra σ l →
    let D := {δ : GeneralLinear n E // IsSigmaRegular σ l δ}
    ∀ (δ₀ : D) (γ₀ : GeneralLinear n F),
      IsNormAssociated σ l δ₀.val γ₀ → IsRegularSemisimple γ₀ →
      ∃ s : D → GeneralLinear n F, Continuous s ∧ s δ₀ = γ₀ ∧
        ∀ δ : D, IsNormAssociated σ l δ.val (s δ) ∧ IsRegularSemisimple (s δ)

set_option maxHeartbeats 950000 in
theorem regularNormRepresentative : RegularNormRepresentativeStatement.{u, v} := by
  classical
  unfold RegularNormRepresentativeStatement
  intro F _ _ _ E _ _ _ _ _ σ l n hσ D δ₀ γ₀ hAssoc₀ hReg₀
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1.symm ▸ hσ.pos)
  choose γ hAssoc hReg using (fun δ : D => δ.property)
  obtain ⟨v₀, hv₀⟩ := regularCyclicBasis F n γ₀.val hReg₀
  choose w hw using (fun δ : D => regularCyclicBasis F n (γ δ).val (hReg δ))
  let B₀ : GeneralLinear n F := hv₀.unit
  let B (δ : D) : GeneralLinear n F := (hw δ).unit
  let s (δ : D) := B₀ * ((B δ)⁻¹ * γ δ * B δ) * B₀⁻¹
  have hVal (δ : D) :
      (s δ).val = B₀.val * charpolyActionMatrix n (γ δ).val.charpoly * (B₀⁻¹).val := by
    change B₀.val * ((B δ)⁻¹ * γ δ * B δ).val * (B₀⁻¹).val = _
    rw [val_cyclicBasis_conjugate (γ δ) (B δ) (w δ) (hw δ).unit_spec]
  let a : F →ₗ[F] E := Algebra.linearMap F E
  obtain ⟨p, hp⟩ := a.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  have hp' (x : F) : p (algebraMap F E x) = x := DFunLike.congr_fun hp x
  have hCoeff (i : Fin n) :
      Continuous (fun δ : D => (γ δ).val.charpoly.coeff i) := by
    have heq (δ : D) : p (coefficients (cyclicNorm σ l δ.val) i) = (γ δ).val.charpoly.coeff i := by
      rw [coefficients_associated (hAssoc δ), coefficients_baseChange, hp']
      rfl
    simp_rw [← heq]
    exact (IsModuleTopology.continuous_of_linearMap p).comp
      ((continuous_charpoly_coefficient (R := E) i).comp
        ((continuous_cyclicNorm σ l).comp continuous_subtype_val))
  have hC : Continuous (fun δ : D => charpolyActionMatrix n (γ δ).val.charpoly) := by
    apply continuous_matrix
    intro i j
    by_cases hj : (j : ℕ) + 1 < n
    · simp only [charpolyActionMatrix_entry, ite_eq_left hj]
      exact continuous_const
    · simp only [charpolyActionMatrix_entry, ite_eq_right hj]
      exact (hCoeff i).neg
  refine ⟨s, Langlands.GeneralLinear.UpperBruhatCoordinates.continuous_generalLinear_of_val ?_, ?_, ?_⟩
  · simp_rw [hVal]
    exact (continuous_const.mul hC).mul continuous_const
  · have hPoly : (γ δ₀).val.charpoly = γ₀.val.charpoly :=
      charpoly_eq_of_baseChange_coefficients hσ
        ((coefficients_associated (hAssoc δ₀)).symm.trans (coefficients_associated hAssoc₀))
    apply Units.ext
    rw [hVal, hPoly, ← val_cyclicBasis_conjugate γ₀ B₀ v₀ hv₀.unit_spec]
    change (B₀ * (B₀⁻¹ * γ₀ * B₀) * B₀⁻¹).val = γ₀.val
    exact congrArg Units.val (by group)
  · intro δ
    let y := B δ * B₀⁻¹
    have hy : s δ = y⁻¹ * γ δ * y := by dsimp only [s, y]; group
    rw [hy]
    refine ⟨?_, ?_⟩
    · simpa using (hAssoc δ).twistedConj hσ.pow_eq_one 1 y
    · change (y⁻¹ * γ δ * y).val.charpoly.Separable
      have hSep : (γ δ).val.charpoly.Separable := hReg δ
      simpa only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj'] using hSep

end Langlands.BaseChange
