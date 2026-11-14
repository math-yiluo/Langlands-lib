import Langlands.Representation.GodementJacquet.WhittakerTorusMellin
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.FiniteFunctionMellinStatement
/-!
# Torus Mellin integrals in diagonal coordinates

Given `FiniteFunctionMellinStatement`, the torus integral
`∫ φ(a_0/a_1, …, a_(n-1)/a_n) J(a) η(a) |a_0 ⋯ a_n|^s da` converges on a right
half-plane and has a rational continuation in `q^(-s)`, for every finite
function `η` and Schwartz–Bruhat functions `φ` on `F^n` and `J` on `F^(n+1)`.
The proof changes variables by the tail products of
`WhittakerTorusCoordinates`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement FiniteFunctionMellinStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped BigOperators

universe uF

namespace Padic
open Langlands.GodementJacquet.WhittakerTorus.Padic hiding initTail ratios torusIntegrand torusIntegrand_tailProd torusMellin torusMellinLocalField torusMellinTopology torusMellinUnitsBorelSpace torusMellinUnitsMeasurableSpace torusMellinValuativeRel
open Langlands.AllField.GodementJacquet.WhittakerTorus.Padic
open Langlands.GodementJacquet.WhittakerTorus
open Langlands.AllField.GodementJacquet.WhittakerTorus
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance torusMellinUnitsMeasurableSpace : MeasurableSpace Fˣ := borel _
local instance torusMellinUnitsBorelSpace : BorelSpace Fˣ := ⟨rfl⟩

variable {n : ℕ}

/-- Adjacent ratios `a_i / a_(i+1)` of diagonal entries, as field elements. -/
def ratios (a : Fin (n + 1) → Fˣ) : Fin n → F :=
  fun i => ((a i.castSucc / a i.succ : Fˣ) : F)

/-- The torus integrand `φ(ratios a) · J(a) · η(a) · |∏ a_i|^s`. -/
def torusIntegrand (φ : SchwartzBruhat (Fin n → F))
    (J : SchwartzBruhat (Fin (n + 1) → F)) (η : (Fin (n + 1) → Fˣ) → ℂ)
    (s : ℂ) (a : Fin (n + 1) → Fˣ) : ℂ :=
  φ (ratios F a) * J (fun i => (a i : F)) * η a *
    (((⟨⟩ : LocalFieldData F).normalizedAbs (∏ i, (a i : F)) : ℝ) : ℂ) ^ s

/-- The Schwartz–Bruhat function `y ↦ φ(y_0, …, y_(n-1)) · J(τ(y))`. -/
def initTail (φ : SchwartzBruhat (Fin n → F))
    (J : SchwartzBruhat (Fin (n + 1) → F)) : SchwartzBruhat (Fin (n + 1) → F) :=
  ⟨_, initTail_mem φ J⟩

/-- In tail-product coordinates the torus integrand is a finite-function Mellin
integrand with weights `k + 1`. -/
theorem torusIntegrand_tailProd (φ : SchwartzBruhat (Fin n → F))
    (J : SchwartzBruhat (Fin (n + 1) → F)) (η : (Fin (n + 1) → Fˣ) → ℂ)
    (s : ℂ) (x : Fin (n + 1) → Fˣ) :
    torusIntegrand F φ J η s (tailProd x) =
      initTail F φ J (fun i => (x i : F)) * η (tailProd x) *
        ∏ i : Fin (n + 1), (((⟨⟩ : LocalFieldData F).normalizedAbs (x i : F) : ℝ) : ℂ) ^
          ((((i : ℕ) + 1 : ℕ) : ℂ) * s) := by
  have hr : ratios F (tailProd x) = fun i : Fin n => (x i.castSucc : F) := by
    funext i
    simp only [ratios, tailProd_div_tailProd]
  have hv : (fun i => ((tailProd x i : Fˣ) : F)) =
      tailProd (fun k => (x k : F)) := by
    funext i
    exact coe_tailProd_units x i
  have hw := cpow_abv_prod_tailProd (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (fun k => (x k : F)) s
  simp only [torusIntegrand, initTail, hr, hv]
  change _ * ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
      (∏ j, tailProd (fun k => (x k : F)) j) : ℝ) : ℂ) ^ s = _
  rw [hw]
  rfl

/-- **Torus Mellin integrals.** Given `FiniteFunctionMellinStatement`, for a
finite function `η` on the torus and Schwartz–Bruhat functions `φ` on `F^n`
and `J` on `F^(n+1)`, the torus integral of `torusIntegrand` converges
absolutely on a right half-plane and has a rational continuation in `q^(-s)`. -/
theorem torusMellin (hFFM : FiniteFunctionMellinStatement.{uF})
    (η : (Fin (n + 1) → Fˣ) → ℂ) (hη : IsFiniteFunction η)
    (φ : SchwartzBruhat (Fin n → F)) (J : SchwartzBruhat (Fin (n + 1) → F)) :
    (∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (torusIntegrand F φ J η s)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
        (fun s => ∫ a, torusIntegrand F φ J η s a
          ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) R := by
  have : SecondCountableTopology F :=
    Langlands.LocalFieldData.secondCountableTopology (⟨⟩ : LocalFieldData F)
  have : SecondCountableTopology Fˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hmp := measurePreserving_tailProd (E := F) (n := n)
  have hme : MeasurableEmbedding (tailProd : (Fin (n + 1) → Fˣ) → _) :=
    (tailProdHomeomorph (G := Fˣ) (n := n)).toHomeomorph.measurableEmbedding
  have hη' : IsFiniteFunction (η ∘ (tailProdEquiv (G := Fˣ) (n := n)).toMonoidHom) :=
    hη.comp _ continuous_tailProd
  obtain ⟨h1, h2, -⟩ := hFFM F (⟨⟩ : LocalFieldData F) (n + 1)
    (fun i => (i : ℕ) + 1) (fun i => Nat.succ_pos _)
    {η ∘ (tailProdEquiv (G := Fˣ) (n := n)).toMonoidHom}
    (fun η₀ h₀ => by rw [Finset.mem_singleton] at h₀; subst h₀; exact hη')
  have key : ∀ s, (fun x => torusIntegrand F φ J η s (tailProd x)) =
      fun x => initTail F φ J (fun i => (x i : F)) *
        (η ∘ (tailProdEquiv (G := Fˣ) (n := n)).toMonoidHom) x *
        ∏ i : Fin (n + 1), (((⟨⟩ : LocalFieldData F).normalizedAbs (x i : F) : ℝ) : ℂ) ^
          ((((i : ℕ) + 1 : ℕ) : ℂ) * s) := fun s =>
    funext fun x => torusIntegrand_tailProd F φ J η s x
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc⟩ := h1 _ (Finset.mem_singleton_self _) (initTail F φ J)
    refine ⟨c, fun s hs => ?_⟩
    rw [← hmp.integrable_comp_emb hme]
    change Integrable (fun x => torusIntegrand F φ J η s (tailProd x)) _
    rw [key s]
    exact hc s hs
  · obtain ⟨R, hR⟩ := h2 _ (Finset.mem_singleton_self _) (initTail F φ J)
    refine ⟨R, ?_⟩
    have he : (fun s => ∫ a, torusIntegrand F φ J η s a
        ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F) =
        fun s => ∫ x, initTail F φ J (fun i => (x i : F)) *
          (η ∘ (tailProdEquiv (G := Fˣ) (n := n)).toMonoidHom) x *
          ∏ i : Fin (n + 1), (((⟨⟩ : LocalFieldData F).normalizedAbs (x i : F) : ℝ) :
            ℂ) ^ ((((i : ℕ) + 1 : ℕ) : ℂ) * s)
          ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F := by
      funext s
      rw [← key s, hmp.integral_comp hme]
    rw [he]
    exact hR

end Padic

end Langlands.AllField.GodementJacquet.WhittakerTorus
