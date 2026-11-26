import Langlands.BaseChange.DeterminantSupportReduction
import Langlands.BaseChange.SatakeCharacter

/-! # Determinant order under spherical base change -/

noncomputable section

namespace Langlands.BaseChange

open Unramified

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

section

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p} {l r : ℕ}
  {b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r}

/-- Base change intertwines twisting by an unramified determinant character
with twisting on the extension side by its degree power. -/
theorem IsUnramifiedBaseChangeHom.determinantTwist_comp (hb : IsUnramifiedBaseChangeHom F E l r b)
    (z : ℂˣ) : (determinantTwist F r z).comp b = b.comp (determinantTwist E r (z ^ l)) := by
  apply AlgHom.ext
  intro φ
  change determinantTwist F r z (b φ) = b (determinantTwist E r (z ^ l) φ)
  apply sub_eq_zero.mp
  apply (satakeCharacter p F r).2
  intro s ω hω
  obtain ⟨η, hη⟩ := (satakeCharacter p E r).1 (Eigenvalues.power s l)
  have hη' : IsSatakeCharacter E r (Eigenvalues.power (Eigenvalues.scale z s) l)
      (η.comp (determinantTwist E r (z ^ l))) := by
    rw [Eigenvalues.power_scale]
    exact IsSatakeCharacter.comp_determinantTwist E r hη (z ^ l)
  have hleft := DFunLike.congr_fun
    (hb _ (ω.comp (determinantTwist F r z)) _ (IsSatakeCharacter.comp_determinantTwist F r hω z) hη') φ
  have hright := DFunLike.congr_fun (hb s ω η hω hη) (determinantTwist E r (z ^ l) φ)
  simp only [map_sub, sub_eq_zero]
  exact hleft.trans hright.symm

/-- A spherical function supported on one determinant order transfers to a
function supported on that order multiplied by the cyclic degree. -/
theorem IsUnramifiedBaseChangeHom.apply_eq_zero_of_det_order_ne
    (hb : IsUnramifiedBaseChangeHom F E l r b) (φ : SphericalHeckeAlgebra E r) (m : ℤ)
    (hφ : ∀ x : GeneralLinear (r + 1) E.Carrier,
      E.canonicalTopologicalData.ord (GeneralLinear.determinant x : E.Carrier) ≠ m → φ x = 0)
    (g : GeneralLinear (r + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) ≠
      (l : ℤ) * m) : b φ g = 0 := by
  let z : ℂˣ := Units.mk0 2 (by norm_num)
  have htwist : determinantTwist E r (z ^ l) φ = (((z ^ l) ^ m : ℂˣ) : ℂ) • φ := by
    apply Hecke.HeckeAlgebra.Corner.ext'
    intro x
    rw [determinantTwist_apply]
    change _ = _ * φ x
    by_cases hx : E.canonicalTopologicalData.ord (GeneralLinear.determinant x : E.Carrier) = m
    · rw [hx]
    · rw [hφ x hx, mul_zero, mul_zero]
  have h := DFunLike.congr_fun (hb.determinantTwist_comp z) φ
  simp only [AlgHom.comp_apply] at h
  rw [htwist, map_smul] at h
  have hg' := congrArg (fun f : SphericalHeckeAlgebra F r => f g) h
  rw [determinantTwist_apply] at hg'
  change (((z ^ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) :
    ℂˣ) : ℂ) * b φ g) = (((z ^ l) ^ m : ℂˣ) : ℂ) * b φ g at hg'
  by_contra hne
  have hpow := Units.val_injective (mul_right_cancel₀ hne hg')
  rw [← zpow_natCast, ← zpow_mul] at hpow
  have hComplex := congrArg (fun a : ℂˣ => (a : ℂ)) hpow
  simp only [Units.val_zpow_eq_zpow_val] at hComplex
  change (2 : ℂ) ^ _ = (2 : ℂ) ^ _ at hComplex
  have hReal : (2 : ℝ) ^ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) =
      (2 : ℝ) ^ ((l : ℤ) * m) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_ofNat] using hComplex
  exact hg (zpow_right_injective₀ (a := (2 : ℝ)) (by norm_num) (by norm_num) hReal)

end

/-- A determinant-homogeneous spherical test has a base change of the
corresponding degree-scaled determinant order. -/
def SphericalDeterminantOrderStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p) (l r : ℕ)
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
    IsUnramifiedBaseChangeHom F E l r b →
    ∀ (φ : SphericalHeckeAlgebra E r) (m : ℤ),
      (∀ x : GeneralLinear (r + 1) E.Carrier,
        E.canonicalTopologicalData.ord (GeneralLinear.determinant x : E.Carrier) ≠ m → φ x = 0) →
      ∀ g : GeneralLinear (r + 1) F.Carrier,
        F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) ≠
          (l : ℤ) * m → b φ g = 0

theorem sphericalDeterminantOrder : SphericalDeterminantOrderStatement.{u, v} :=
  fun _ _ _ _ _ _ _ hb => hb.apply_eq_zero_of_det_order_ne

end Langlands.BaseChange
