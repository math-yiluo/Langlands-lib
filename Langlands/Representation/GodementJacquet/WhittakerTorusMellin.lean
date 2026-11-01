import Langlands.Representation.GodementJacquet.WhittakerTorusCoordinates
import Langlands.Representation.RankinSelberg.FiniteFunctionMellinStatement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Representation.RankinSelberg.AnalyticStatement

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

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped BigOperators

universe uF

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance torusMellinTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance torusMellinValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance torusMellinLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance torusMellinUnitsMeasurableSpace : MeasurableSpace F.Carrierˣ := borel _
local instance torusMellinUnitsBorelSpace : BorelSpace F.Carrierˣ := ⟨rfl⟩

variable {n : ℕ}

/-- Adjacent ratios `a_i / a_(i+1)` of diagonal entries, as field elements. -/
def ratios (a : Fin (n + 1) → F.Carrierˣ) : Fin n → F.Carrier :=
  fun i => ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier)

/-- The torus integrand `φ(ratios a) · J(a) · η(a) · |∏ a_i|^s`. -/
def torusIntegrand (φ : SchwartzBruhat (Fin n → F.Carrier))
    (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (η : (Fin (n + 1) → F.Carrierˣ) → ℂ)
    (s : ℂ) (a : Fin (n + 1) → F.Carrierˣ) : ℂ :=
  φ (ratios F a) * J (fun i => (a i : F.Carrier)) * η a *
    ((F.canonicalTopologicalData.normalizedAbs (∏ i, (a i : F.Carrier)) : ℝ) : ℂ) ^ s

/-- The Schwartz–Bruhat function `y ↦ φ(y_0, …, y_(n-1)) · J(τ(y))`. -/
def initTail (φ : SchwartzBruhat (Fin n → F.Carrier))
    (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)) : SchwartzBruhat (Fin (n + 1) → F.Carrier) :=
  ⟨_, initTail_mem φ J⟩

/-- In tail-product coordinates the torus integrand is a finite-function Mellin
integrand with weights `k + 1`. -/
theorem torusIntegrand_tailProd (φ : SchwartzBruhat (Fin n → F.Carrier))
    (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (η : (Fin (n + 1) → F.Carrierˣ) → ℂ)
    (s : ℂ) (x : Fin (n + 1) → F.Carrierˣ) :
    torusIntegrand F φ J η s (tailProd x) =
      initTail F φ J (fun i => (x i : F.Carrier)) * η (tailProd x) *
        ∏ i : Fin (n + 1), ((F.canonicalTopologicalData.normalizedAbs (x i : F.Carrier) : ℝ) : ℂ) ^
          ((((i : ℕ) + 1 : ℕ) : ℂ) * s) := by
  have hr : ratios F (tailProd x) = fun i : Fin n => (x i.castSucc : F.Carrier) := by
    funext i
    simp only [ratios, tailProd_div_tailProd]
  have hv : (fun i => ((tailProd x i : F.Carrierˣ) : F.Carrier)) =
      tailProd (fun k => (x k : F.Carrier)) := by
    funext i
    exact coe_tailProd_units x i
  have hw := cpow_abv_prod_tailProd (normalizedAbsoluteValue F.canonicalTopologicalData)
    (fun k => (x k : F.Carrier)) s
  simp only [torusIntegrand, initTail, hr, hv]
  change _ * ((normalizedAbsoluteValue F.canonicalTopologicalData
      (∏ j, tailProd (fun k => (x k : F.Carrier)) j) : ℝ) : ℂ) ^ s = _
  rw [hw]
  rfl

/-- **Torus Mellin integrals.** Given `FiniteFunctionMellinStatement`, for a
finite function `η` on the torus and Schwartz–Bruhat functions `φ` on `F^n`
and `J` on `F^(n+1)`, the torus integral of `torusIntegrand` converges
absolutely on a right half-plane and has a rational continuation in `q^(-s)`. -/
theorem torusMellin (hFFM : FiniteFunctionMellinStatement.{uF})
    (η : (Fin (n + 1) → F.Carrierˣ) → ℂ) (hη : IsFiniteFunction η)
    (φ : SchwartzBruhat (Fin n → F.Carrier)) (J : SchwartzBruhat (Fin (n + 1) → F.Carrier)) :
    (∃ c : ℝ, ∀ s : ℂ, c < s.re → Integrable (torusIntegrand F φ J η s)
      (Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier)) ∧
    ∃ R : RationalFunctions,
      HasRationalContinuation F.canonicalTopologicalData.residueCardinality
        (fun s => ∫ a, torusIntegrand F φ J η s a
          ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) R := by
  have : SecondCountableTopology F.Carrier :=
    PadicField.TopologicalData.secondCountableTopology F.canonicalTopologicalData
  have : SecondCountableTopology F.Carrierˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hmp := measurePreserving_tailProd (E := F.Carrier) (n := n)
  have hme : MeasurableEmbedding (tailProd : (Fin (n + 1) → F.Carrierˣ) → _) :=
    (tailProdHomeomorph (G := F.Carrierˣ) (n := n)).toHomeomorph.measurableEmbedding
  have hη' : IsFiniteFunction (η ∘ (tailProdEquiv (G := F.Carrierˣ) (n := n)).toMonoidHom) :=
    hη.comp _ continuous_tailProd
  obtain ⟨h1, h2, -⟩ := hFFM p inferInstance F F.canonicalTopologicalData (n + 1)
    (fun i => (i : ℕ) + 1) (fun i => Nat.succ_pos _)
    {η ∘ (tailProdEquiv (G := F.Carrierˣ) (n := n)).toMonoidHom}
    (fun η₀ h₀ => by rw [Finset.mem_singleton] at h₀; subst h₀; exact hη')
  have key : ∀ s, (fun x => torusIntegrand F φ J η s (tailProd x)) =
      fun x => initTail F φ J (fun i => (x i : F.Carrier)) *
        (η ∘ (tailProdEquiv (G := F.Carrierˣ) (n := n)).toMonoidHom) x *
        ∏ i : Fin (n + 1), ((F.canonicalTopologicalData.normalizedAbs (x i : F.Carrier) : ℝ) : ℂ) ^
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
        ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier) =
        fun s => ∫ x, initTail F φ J (fun i => (x i : F.Carrier)) *
          (η ∘ (tailProdEquiv (G := F.Carrierˣ) (n := n)).toMonoidHom) x *
          ∏ i : Fin (n + 1), ((F.canonicalTopologicalData.normalizedAbs (x i : F.Carrier) : ℝ) :
            ℂ) ^ ((((i : ℕ) + 1 : ℕ) : ℂ) * s)
          ∂Measure.pi fun _ : Fin (n + 1) => localMultiplicativeHaar F.Carrier := by
      funext s
      rw [← key s, hmp.integral_comp hme]
    rw [he]
    exact hR

end Padic

end Langlands.GodementJacquet.WhittakerTorus
