import Langlands.BaseChange.SatakeTwoBlockSection
import Langlands.Representation.GodementJacquet.TwoBlockSchwartz

/-! Satake evaluation on a two-block constant term given by a finite spherical sum. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.Correspondence Langlands.GeneralLinear Langlands.RankinSelberg
open Langlands.RankinSelberg.TwoBlockJacquet Langlands.GodementJacquet.TwoBlock
open Langlands.Unramified

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance satakeBlockFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance satakeBlockFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance satakeBlockFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance satakeBlockGLSigmaCompact (n : ℕ) : SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_sigmaCompactSpace F.Carrier n
local instance satakeBlockMatrixSigmaCompact (a b : ℕ) :
    SigmaCompactSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SigmaCompactSpace (Fin a → Fin b → F.Carrier))

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [dx.IsAddHaarMeasure]

local notation "B" => succBlockShape m h
local notation "𝒪" => Valuation.integer (ValuativeRel.valuation F.Carrier)

set_option maxHeartbeats 800000 in
/-- The ambient Satake character evaluates a finite spherical expansion of the
normalized constant term by the product of the characters at the block parameters. -/
theorem satakeCharacter_eq_sum_of_twoBlock_constantTerm
    (hdx : dx {x | ∀ a b, x a b ∈ 𝒪} = 1) (f : SphericalHeckeAlgebra F t)
    {J : Type*} [Fintype J] (α : J → SphericalHeckeAlgebra F (m 0))
    (β : J → SphericalHeckeAlgebra F (m 1))
    (hCT : ∀ L : (B).Levi F.Carrier,
      (F.canonicalTopologicalData.leviHalfModulus B L : ℂ) *
        (∫ x, f (parabolicPoint h (L, x)) ∂dx) = ∑ j, α j (L 0) * β j (L 1))
    (z : Fin (t + 1) → ℂˣ) (ω : SphericalHeckeAlgebra F t →ₐ[ℂ] ℂ)
    (ω₀ : SphericalHeckeAlgebra F (m 0) →ₐ[ℂ] ℂ)
    (ω₁ : SphericalHeckeAlgebra F (m 1) →ₐ[ℂ] ℂ)
    (hω : IsSatakeCharacter F t (Eigenvalues.ofTuple z) ω)
    (hω₀ : IsSatakeCharacter F (m 0) (Eigenvalues.ofTuple (fun a => z ((B).index 0 a))) ω₀)
    (hω₁ : IsSatakeCharacter F (m 1) (Eigenvalues.ofTuple (fun a => z ((B).index 1 a))) ω₁) :
    ω f = ∑ j, ω₀ (α j) * ω₁ (β j) := by
  let μ (i : Fin 2) := generalLinearHaar F.Carrier (m i)
  let s (i : Fin 2) := sphericalPrincipalSeriesSection F (fun a => z ((B).index i a))
  let g (q : (B).Levi F.Carrier × _) :=
    f (parabolicPoint h q) * sphericalPrincipalSeriesSection F z (parabolicPoint h q)
  have hI := integrable_integral_parabolicPoint_of_right_sphericalInvariant F h dx hdx
    (integrable_mul_sphericalPrincipalSeriesSection F z f) (fun x k => by
      rw [Hecke.HeckeAlgebra.Corner.rightInvariant _ _ _ f k x,
        sphericalPrincipalSeriesSection_rightInvariant F z x k])
  have hInner (L : (B).Levi F.Carrier) :
      ∫ x, g (L, x) ∂dx = ∑ j, (α j (L 0) * s 0 (L 0)) * (β j (L 1) * s 1 (L 1)) := by
    let δ := (F.canonicalTopologicalData.leviHalfModulus B L : ℂ)
    have hg (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
        g (L, x) = f (parabolicPoint h (L, x)) * (δ * (s 0 (L 0) * s 1 (L 1))) := by
      dsimp only [g, δ, s]
      rw [sphericalPrincipalSeriesSection_parabolicPoint F h, Fin.prod_univ_two]
    simp_rw [hg]
    rw [integral_mul_const, ← mul_assoc, mul_comm (∫ x, f (parabolicPoint h (L, x)) ∂dx) δ,
      hCT L, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hI₀ (j : J) : Integrable (fun a => α j a * s 0 a) (μ 0) := by
    change Integrable _ (generalLinearHaar F.Carrier (m 0))
    rw [← sphericalHaar_eq_generalLinearHaar]
    exact integrable_mul_sphericalPrincipalSeriesSection F _ (α j)
  have hI₁ (j : J) : Integrable (fun b => β j b * s 1 b) (μ 1) := by
    change Integrable _ (generalLinearHaar F.Carrier (m 1))
    rw [← sphericalHaar_eq_generalLinearHaar]
    exact integrable_mul_sphericalPrincipalSeriesSection F _ (β j)
  calc
    ω f = ∫ x, f x * sphericalPrincipalSeriesSection F z x ∂(sphericalHaar F t) :=
      satakeCharacter_eq_integral_sphericalPrincipalSeriesSection F z ω hω f
    _ = ∫ q, g q ∂(parabolicMeasure F h dx) := hI.2.symm
    _ = ∫ L, ∫ x, g (L, x) ∂dx ∂(Measure.pi μ) := integral_prod g hI.1
    _ = ∫ L : (B).Levi F.Carrier,
          ∑ j, (α j (L 0) * s 0 (L 0)) * (β j (L 1) * s 1 (L 1)) ∂(Measure.pi μ) :=
      integral_congr_ae (ae_of_all _ hInner)
    _ = ∑ j, ∫ L : (B).Levi F.Carrier,
          (α j (L 0) * s 0 (L 0)) * (β j (L 1) * s 1 (L 1)) ∂(Measure.pi μ) :=
      integral_finsetSum _ (fun j _ => integrable_pi_two_mul μ (hI₀ j) (hI₁ j))
    _ = ∑ j, ω₀ (α j) * ω₁ (β j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_pi_two_mul μ (fun a => α j a * s 0 a) (fun b => β j b * s 1 b)]
      dsimp only [μ, s]
      rw [← sphericalHaar_eq_generalLinearHaar F (m 0),
        ← sphericalHaar_eq_generalLinearHaar F (m 1),
        ← satakeCharacter_eq_integral_sphericalPrincipalSeriesSection F _ ω₀ hω₀ (α j),
        ← satakeCharacter_eq_integral_sphericalPrincipalSeriesSection F _ ω₁ hω₁ (β j)]

end Langlands.BaseChange
