import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Representation.Classification.SquareIntegrableLanglandsClassificationReduction
import Langlands.Representation.Unitary.CentralCharacterProof

/-!
# Essentially square-integrable representations with a unitary central character

For a nonarchimedean local field `F` and `n > 0`, a representation `ρ` of `GL_n(F)` on a
nonzero space that is essentially square-integrable (`ρ = |det|^s ⊗ ρ₀` with `ρ₀`
square-integrable modulo the center) and has a unitary central character is
square-integrable modulo the center: comparing the two unitary central characters at the
scalar matrix of a uniformizer forces `s = 0`. In particular an irreducible admissible
unitarizable essentially square-integrable representation is square-integrable. See the
paired Markdown.
-/

noncomputable section

open scoped NNReal
open MeasureTheory

namespace Langlands.JacquetLanglands

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

variable (F n) in
/-- The scalar matrix of the chosen uniformizer `LocalField.uniformizer F`, as an element of
the center of `GL_n(F)`. -/
def uniformizerScalarCenter : Subgroup.center (GeneralLinear n F) :=
  GeneralLinear.scalarToCenter
    (Units.mk0 (LocalField.uniformizer F) (LocalField.uniformizer_ne_zero F))

/-- For `n > 0`, the absolute value of the determinant of the scalar matrix of a uniformizer
is `q^{-n} ≠ 1`, where `q` is the residue cardinality. -/
theorem determinantNorm_uniformizerScalarCenter_ne_one (hn : 0 < n) :
    ((determinantNorm F n (uniformizerScalarCenter F n : GeneralLinear n F) : ℝ≥0) : ℝ) ≠ 1 := by
  rw [determinantNorm_coe]
  have hdet : (GeneralLinear.determinant (uniformizerScalarCenter F n : GeneralLinear n F) : F) =
      LocalField.uniformizer F ^ n := by
    change Matrix.det (Matrix.scalar (Fin n) (LocalField.uniformizer F)) = _
    rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hdet, map_pow, LocalField.residueNormalizedAbsoluteValue_uniformizer, zpow_neg_one]
  apply ne_of_lt
  apply pow_lt_one₀ (inv_nonneg.mpr (Nat.cast_nonneg _))
  · exact inv_lt_one_of_one_lt₀ (by exact_mod_cast LocalField.residueCardinality_gt_one F)
  · exact Nat.ne_of_gt hn

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- For `n > 0`, an essentially square-integrable representation of `GL_n(F)` on a nonzero
space with a unitary central character is square-integrable modulo the center. -/
theorem IsEssentiallySquareIntegrable.isSquareIntegrable_of_unitaryCentralCharacter
    (hn : 0 < n) [Nontrivial V] {ρ : Representation ℂ (GeneralLinear n F) V}
    (hρ : IsEssentiallySquareIntegrable ρ) (c : UnitaryCentralCharacter ρ) :
    IsSquareIntegrable ρ := by
  obtain ⟨s, hs⟩ := hρ
  let := centralQuotientMeasurableSpace F n
  have := centralQuotientBorelSpace F n
  obtain ⟨μ, hμ⟩ := exists_isHaarMeasure_centralQuotient F n
  obtain ⟨-, cs, -⟩ := hs μ
  have c0 :
      UnitaryCentralCharacter (Langlands.realPowerTwist (determinantNorm F n) (-(0 : ℝ)) ρ) := by
    simpa only [neg_zero, realPowerTwist_zero] using c
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hs0 : s = 0 :=
    Classification.exponent_eq_of_unitaryCentralCharacter (determinantNorm F n) cs c0 hv
      (uniformizerScalarCenter F n) (determinantNorm_uniformizerScalarCenter_ne_one hn)
  simpa only [hs0, neg_zero, realPowerTwist_zero] using hs

/-- For `n > 0`, an irreducible, unitarizable, essentially square-integrable representation
of `GL_n(F)` is square-integrable modulo the center. -/
theorem IsEssentiallySquareIntegrable.isSquareIntegrable_of_isUnitarizable
    (hn : 0 < n) {ρ : Representation ℂ (GeneralLinear n F) V}
    (hρ : IsEssentiallySquareIntegrable ρ) (hirr : ρ.IsIrreducible) (hu : IsUnitarizable ρ) :
    IsSquareIntegrable ρ := by
  let := hirr
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F)) ρ.asModule
  obtain ⟨c⟩ := unitarizableCentralCharacter ρ hρ.isAdmissible hirr hu
  exact hρ.isSquareIntegrable_of_unitaryCentralCharacter hn c

end Langlands.JacquetLanglands
