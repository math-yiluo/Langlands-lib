import Langlands.BaseChange.DeterminantSupportReduction
import Langlands.BaseChange.EllipticNormCriterionStatement
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof

/-! # Off-norm vanishing on the elliptic set -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Langlands.JacquetLanglands Langlands.TraceFormula Langlands.Unramified
open Langlands.QuotientIntegration MeasureTheory

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l n : ℕ}

/-- On the regular elliptic set, the elliptic norm criterion identifies the norm locus
with determinant orders divisible by the degree of the unramified extension. -/
theorem isNorm_elliptic_iff_dvd_det (hcriterion : EllipticNormCriterionStatement.{u, v})
    (hcyc : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) {γ : GeneralLinear n F.Carrier}
    (hγ : IsRegularElliptic γ) :
    IsNorm σ l γ ↔
      (l : ℤ) ∣ F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier) := by
  let : FiniteDimensional F.Carrier E.Carrier := hcyc.1
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  have hmem := LocalClassField.unramifiedNormMembership p F E F.canonicalTopologicalData
    E.canonicalTopologicalData he.symm (GeneralLinear.determinant γ)
  rw [hcyc.2.1] at hmem
  exact (hcriterion F.Carrier E.Carrier σ l n hcyc γ hγ).trans hmem

/-- The off-norm vanishing branch for regular elliptic elements, under the
elliptic norm criterion and the Satake character statements. -/
def EllipticNonNormVanishingReductionStatement : Prop :=
  EllipticNormCriterionStatement.{u, v} →
  SatakeCharacterStatement.{u} → SatakeCharacterStatement.{v} →
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (l r : ℕ),
    IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex →
    ∀ (b : SphericalHeckeAlgebra E r →ₐ[ℂ] SphericalHeckeAlgebra F r),
      IsUnramifiedBaseChangeHom F E l r b →
      ∀ (φ : SphericalHeckeAlgebra E r) (γ : GeneralLinear (r + 1) F.Carrier),
        IsRegularElliptic γ → ¬ IsNorm σ l γ →
        ∀ (ν : Measure (LeftQuotient (glCentralizer γ))), orbitalIntegral γ ν ⇑(b φ) = 0

theorem ellipticNonNormVanishingReduction : EllipticNonNormVanishingReductionStatement.{u, v} := by
  intro hcriterion hSatakeF hSatakeE p hp F E _ _ σ l r hcyc he b hb φ γ hγ hnot ν
  have hnorm := isNorm_elliptic_iff_dvd_det hcriterion hcyc he hγ
  exact determinantSupportReduction hSatakeF hSatakeE p F E l r hcyc.pos.ne' b hb φ γ
    (fun hdvd => hnot (hnorm.mpr hdvd)) ν

end Langlands.BaseChange
