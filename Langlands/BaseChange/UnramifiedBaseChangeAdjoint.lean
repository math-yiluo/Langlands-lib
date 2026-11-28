import Langlands.BaseChange.SatakeCharacter
import Langlands.Automorphic.ContragredientHeckeTransfer
import Langlands.Representation.Hecke.UnimodularStar
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration
import Langlands.Representation.Unramified.UnitarySpectrumConjugation

/-! # Adjoint compatibility of spherical base change -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ComplexConjugate

namespace Langlands.Unramified

open Correspondence

universe u

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime]

/-- Inversion preserves spherical Haar measure. -/
theorem sphericalHaar_isInvInvariant (F : PadicField.{u} p) (r : ℕ) :
    IsInvInvariant (sphericalHaar F r) := by
  rw [sphericalHaar_eq_generalLinearHaar F r]
  exact (RankinSelberg.generalLinearHaarSymmetries F.Carrier r).1

end Langlands.Unramified

namespace Langlands.BaseChange

open Correspondence Unramified

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

variable {p : ℕ} [Fact p.Prime]

local instance (F : PadicField.{u} p) (r : ℕ) : IsInvInvariant (sphericalHaar F r) :=
  sphericalHaar_isInvInvariant F r

local instance (F : PadicField.{u} p) (r : ℕ) : IsMulRightInvariant (sphericalHaar F r) := by
  rw [sphericalHaar_eq_generalLinearHaar F r]
  exact RankinSelberg.generalLinearHaarRightInvariant F.Carrier r

/-- Unramified base change commutes with the spherical Hecke adjoint. -/
def UnramifiedBaseChangeAdjointStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p) {l r : ℕ}
    (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
    IsUnramifiedBaseChangeHom F E l r b →
      ∀ φ : SphericalHeckeAlgebra E r, b (star φ) = star (b φ)

private theorem standardHeckeLast_mul_star (F : PadicField.{u} p) {r : ℕ}
    (i : Fin (r + 2)) :
    standardHeckeElement F r (Fin.last (r + 1)) * star (standardHeckeElement F r i) =
      standardHeckeElement F r i.rev := by
  let t := standardDiagonal F r (Fin.last (r + 1))
  have ht : t ∈ Subgroup.center (GeneralLinear (r + 1) F.Carrier) := by
    rw [Subgroup.mem_center_iff]
    intro x
    exact (PairedHecke.standardDiagonal_last_commute F x).symm
  have hn := Subgroup.center_le_normalizer (sphericalOpenSubgroup F r).toSubgroup ht
  apply Hecke.HeckeAlgebra.Corner.ext'
  intro x
  change (Hecke.HeckeAlgebra.Corner.doubleCoset (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r) (sphericalHaar F r) t *
      star (standardHeckeElement F r i)) x = _
  rw [Hecke.HeckeAlgebra.Corner.doubleCoset_mul_apply_of_mem_normalizer _ _ _ hn,
    Hecke.HeckeAlgebra.Corner.star_apply, PairedHecke.conj_standardHeckeElement,
    PairedHecke.standardHeckeElement_inv]
  change standardHeckeElement F r i.rev (t * (t⁻¹ * x)) = _
  rw [mul_inv_cancel_left]

private def adjointCharacter (F : PadicField.{u} p) (r : ℕ)
    (ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ) : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ where
  toFun f := conj (ω (star f))
  map_one' := by rw [star_one, map_one, map_one]
  map_mul' f g := by rw [star_mul, map_mul, map_mul, mul_comm]
  map_zero' := by rw [star_zero, map_zero, map_zero]
  map_add' f g := by rw [star_add, map_add, map_add]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one, map_smul, map_one, smul_eq_mul,
      mul_one, Algebra.algebraMap_self_apply]
    exact star_star c

private def adjointSpectrum {n : ℕ} (s : Eigenvalues n) : Eigenvalues n :=
  conjSpectrum (s.map Inv.inv)

private theorem adjointSpectrum_power {n : ℕ} (s : Eigenvalues n) (l : ℕ) :
    adjointSpectrum (s.power l) = (adjointSpectrum s).power l := by
  simp [adjointSpectrum, Eigenvalues.power, conjSpectrum, Sym.map_map, inv_pow]

private theorem adjointCharacter_isSatake (F : PadicField.{u} p) {r : ℕ}
    {s : Eigenvalues (r + 1)} {ω : SphericalHeckeAlgebra F r →ₐ[ℂ] ℂ}
    (hω : IsSatakeCharacter F r s ω) :
    IsSatakeCharacter F r (adjointSpectrum s) (adjointCharacter F r ω) := by
  intro i
  change conj (ω (star (standardHeckeElement F r i))) =
    standardHeckeScalar F (conjSpectrum (s.map Inv.inv)) i
  rw [standardHeckeScalar_conjSpectrum]
  congr 1
  have h := congrArg ω (standardHeckeLast_mul_star F i)
  rw [map_mul, hω (Fin.last (r + 1)), hω i.rev] at h
  apply mul_left_cancel₀ (standardHeckeScalar_last_ne_zero F s)
  calc
    standardHeckeScalar F s (Fin.last (r + 1)) * ω (star (standardHeckeElement F r i)) =
        standardHeckeScalar F s i.rev := h
    _ = standardHeckeScalar F (s.map Inv.inv) i *
        standardHeckeScalar F s (Fin.last (r + 1)) :=
      (PairedHecke.standardHeckeScalar_map_inv_mul_last F s i).symm
    _ = _ := mul_comm _ _

/-- The conjugate of a Satake character evaluated on an adjoint is the character
at the conjugate reciprocal parameter. Taking powers commutes with this change
of parameter. -/
theorem unramifiedBaseChangeAdjoint : UnramifiedBaseChangeAdjointStatement.{u, v} := by
  intro p _ F E l r b hb φ
  apply sub_eq_zero.mp
  apply (satakeCharacter p F r).2
  intro s ωF hωF
  obtain ⟨ωE, hωE⟩ := (satakeCharacter p E r).1 (s.power l)
  have h := DFunLike.congr_fun (hb s ωF ωE hωF hωE) (star φ)
  change ωF (b (star φ)) = ωE (star φ) at h
  have hE' : IsSatakeCharacter E r ((adjointSpectrum s).power l) (adjointCharacter E r ωE) :=
    adjointSpectrum_power s l ▸ adjointCharacter_isSatake E hωE
  have h' := DFunLike.congr_fun
    (hb (adjointSpectrum s) (adjointCharacter F r ωF) (adjointCharacter E r ωE)
      (adjointCharacter_isSatake F hωF) hE') φ
  change conj (ωF (star (b φ))) = conj (ωE (star φ)) at h'
  rw [map_sub, h, (starRingEnd ℂ).injective h', sub_self]

end Langlands.BaseChange
