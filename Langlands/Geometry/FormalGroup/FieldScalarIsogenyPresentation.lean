import Langlands.Geometry.FormalGroup.ScalarCompositesIsogeny
import Langlands.Geometry.FormalGroup.IsogenyKernelTorsion
import Langlands.Geometry.FormalGroup.KernelQuotient
import Langlands.Geometry.FormalGroup.PointFactorization
import Langlands.Geometry.FormalGroup.ScalarIsogenyPresentation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-! # Integral numerators of tensor quasi-isogenies over a field -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory
open scoped nonZeroDivisors

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] {π : O}
variable {σ τ : Type} [Finite σ] [Finite τ]

section Localization

variable [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type w} [Field F] [Algebra O F] [IsFractionRing O F]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

namespace RationalHom

/-- Every actual tensor homomorphism has a uniformizer-power denominator. -/
theorem exists_uniformizerPower_ofHom (hπ : Irreducible π) (z : RationalHom F M N) :
    ∃ (n : ℕ) (f : Hom M N), (algebraMap O F π) ^ n • z = ofHom f := by
  let i := ofHom (F := F) (M := M) (N := N)
  let : IsLocalizedModule O⁰ i := IsLocalization.tensorProduct_isLocalizedModule O⁰ F
  obtain ⟨⟨f, a⟩, ha⟩ := IsLocalizedModule.surj O⁰ i z
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero a.property) hπ
  change (a : O) • z = i f at ha
  rw [he, mul_smul] at ha
  refine ⟨n, (↑e⁻¹ : O) • f, ?_⟩
  rw [← map_pow, IsScalarTower.algebraMap_smul F]
  have h := congrArg (fun y : RationalHom F M N => (↑e⁻¹ : O) • y) ha
  simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, ← i.map_smul] using h

/-- Scalar divisibility of the source makes its integral Hom inject into the tensor Hom. -/
theorem ofHom_injective_of_piDivisible (hπ : Irreducible π) (hM : M.IsPiDivisible π) :
    Function.Injective (ofHom (F := F) (M := M) (N := N)) := by
  let i := ofHom (F := F) (M := M) (N := N)
  let : IsLocalizedModule O⁰ i := IsLocalization.tensorProduct_isLocalizedModule O⁰ F
  intro f g hfg
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists O⁰ i).1 hfg
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero a.property) hπ
  change (a : O) • f = (a : O) • g at ha
  rw [he, mul_smul, mul_smul] at ha
  have h : (π ^ n) • f = (π ^ n) • g := e.isUnit.smul_left_cancel.mp ha
  apply (hM.scalarPower_locallySurjective n).comp_right_cancel
  simpa only [scalarHom, Hom.comp_smul, Hom.comp_id] using h

end RationalHom

namespace QuasiIsogeny

/-- Integral numerators of the two inverse tensors compose to the corresponding scalar powers. -/
theorem scalarComposites (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {n m : ℕ} {f : Hom M N} {g : Hom N M}
    (hf : (algebraMap O F π) ^ n • e.hom = RationalHom.ofHom f)
    (hg : (algebraMap O F π) ^ m • e.inv = RationalHom.ofHom g) :
    g.comp f = M.scalarHom (π ^ (m + n)) ∧
      f.comp g = N.scalarHom (π ^ (m + n)) := by
  constructor
  · apply RationalHom.ofHom_injective_of_piDivisible (F := F) hπ hM
    rw [RationalHom.ofHom_comp, ← hf, ← hg, RationalHom.smul_comp, RationalHom.comp_smul,
      e.inv_hom, scalarHom, map_smul, ← IsScalarTower.algebraMap_smul F (π ^ (m + n)),
      RationalHom.ofHom_id, map_pow, pow_add, smul_smul]
  · apply RationalHom.ofHom_injective_of_piDivisible (F := F) hπ hN
    rw [RationalHom.ofHom_comp, ← hf, ← hg, RationalHom.smul_comp, RationalHom.comp_smul,
      e.hom_inv, scalarHom, map_smul, ← IsScalarTower.algebraMap_smul F (π ^ (m + n)),
      RationalHom.ofHom_id, map_pow, pow_add, smul_smul,
      mul_comm ((algebraMap O F π) ^ n)]

end QuasiIsogeny
end Localization

section Field

variable {k F : Type v} [Field k] [Algebra O k] [Field F] [Algebra O F]
variable {M : ModuleLaw O k σ} {N : ModuleLaw O k τ}

namespace Hom

/-- Over a field the closed subkernel of a scalar power is finite projective.
The other scalar composite gives fppf local surjectivity of the numerator. -/
theorem isIsogeny_of_scalarComposites {f : Hom M N} {g : Hom N M}
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) {j : ℕ}
    (hgf : g.comp f = M.scalarHom (π ^ j)) (hfg : f.comp g = N.scalarHom (π ^ j)) :
    f.IsIsogeny :=
  isIsogeny_of_scalarComposites_overRing hM hN hgf hfg

end Hom

namespace QuasiIsogeny

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O F]

/-- Any integral homomorphism that clears a uniformizer denominator of an
invertible tensor is an isogeny over the field. -/
theorem isIsogeny_of_clearsDenominator (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π)
    {n : ℕ} {f : Hom M N}
    (hf : (algebraMap O F π) ^ n • e.hom = RationalHom.ofHom f) :
    f.IsIsogeny := by
  obtain ⟨m, g, hg⟩ := RationalHom.exists_uniformizerPower_ofHom hπ e.inv
  exact (e.scalarComposites hπ hM hN hf hg).elim (Hom.isIsogeny_of_scalarComposites hM hN)

/-- Choose a genuine integral isogeny numerator for a field-valued tensor quasi-isogeny. -/
def scalarIsogenyPresentation (e : QuasiIsogeny F M N) (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) :
    RationalHom.ScalarIsogenyPresentation π e.hom :=
  let h := RationalHom.exists_uniformizerPower_ofHom hπ e.hom
  let hf := h.choose_spec.choose_spec
  ⟨h.choose, h.choose_spec.choose, e.isIsogeny_of_clearsDenominator hπ hM hN hf, hf⟩

end QuasiIsogeny
end Field

end Langlands.FormalGroup.ModuleLaw
