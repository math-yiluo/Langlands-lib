import Langlands.AlgebraicGeometry.Picard.NonzeroEndomorphismMixedEulerPositiveStatement
import Langlands.AlgebraicGeometry.Picard.NonzeroPullbackPowerSection
import Langlands.AlgebraicGeometry.Picard.MixedEulerSectionSupport
import Langlands.AlgebraicGeometry.Picard.MixedEulerCoefficientScaling

/-! # Positivity of the mixed Euler coefficient for a nonzero pullback -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The pullback mixed coefficient is positive over any field in positive dimension. -/
theorem mixedLineBundleEulerCoefficient_pos_pullback
    {k : Type u} [Field k] (A : AbelianScheme (Spec (CommRingCat.of k)))
    (d : ℕ) (hg : A.HasRelativeDimension (d + 1))
    (L : LineBundle A.X.left) (hL : L.IsAmple) (f : A ⟶ A) (hf : f ≠ 0) :
    0 < mixedLineBundleEulerCoefficient A.X.hom L
      ((LineBundle.pullback (hom f)).obj L) (d + 1) := by
  let : IsIntegral A.X.left := field_isIntegral A
  let : IsNoetherian A.X.left := field_isNoetherian A
  let : A.X.left.IsSeparated := field_isSeparated A
  obtain ⟨n, hn, s, hs, hz⟩ := nonzeroPullbackPowerSection A L hL f hf
  let N := (LineBundle.pullback (hom f)).obj L
  let Nn : LineBundle A.X.left :=
    ⟨tensorPow N.obj n, tensorPow_isLocallyFreeRankOne A.X.left N n⟩
  have hp := mixedLineBundleEulerCoefficient_pos_of_section A.X.hom d hg
    inferInstance L Nn hL s hs hz
  have hdim : topologicalKrullDim A.X.left ≤ d + 1 := by
    rw [field_topologicalKrullDim hg]
    exact le_rfl
  rw [mixedLineBundleEulerCoefficient_tensorPow A.X.hom L N d hdim n] at hp
  exact pos_of_mul_pos_right hp (Nat.cast_nonneg n)

/-- Exact full-universe proof of the existing geometric mixed positivity statement. -/
theorem nonzeroEndomorphismMixedEulerPositive :
    NonzeroEndomorphismMixedEulerPositiveStatement.{u} := by
  intro k _ _ _ A g hg hdim L hL f hf
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hg)
  exact mixedLineBundleEulerCoefficient_pos_pullback A d hdim L hL f hf

end Langlands.AbelianScheme
