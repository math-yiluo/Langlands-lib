import Langlands.HarmonicAnalysis.Distribution.RenardHaarLeftProof
import Langlands.HarmonicAnalysis.Distribution.TensorProduct

/-! # Factorization of a distribution invariant under the first product coordinate -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open MeasureTheory
open Hecke.TestFunction (pullback)
open scoped _root_.Topology

variable {G Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace Y]

/-- Invariance under translation of the first coordinate of a product. -/
def IsLeftInvariantInFirstFactor (D : Distribution (G × Y)) : Prop :=
  ∀ a : G, pushforward ((Homeomorph.mulLeft a).prodCongr (Homeomorph.refl Y)) D = D

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] [T2Space Y]
  (μ : Measure G) [μ.IsHaarMeasure]

/-- A distribution invariant under left translation in the first factor is Haar
integration there, tensored with a unique distribution in the second factor. -/
def HaarTensorFactorizationStatement (D : Distribution (G × Y)) : Prop :=
  IsLeftInvariantInFirstFactor D → ∃! S : Distribution Y, D = tensor (ofMeasure μ) S

omit [IsTopologicalGroup G] in
private theorem exists_integralOneTest : ∃ f : SchwartzBruhat G, ofMeasure μ f = 1 := by
  obtain ⟨U, hUc, hU, h1, _⟩ := Langlands.HarmonicAnalysis.exists_compact_clopen
    (Filter.univ_mem : Set.univ ∈ 𝓝 (1 : G))
  let f := Hecke.TestFunction.characteristic hU hUc
  have hf : ofMeasure μ f ≠ 0 :=
    RenardHaar.ofMeasure_characteristic_ne_zero μ hU hUc ⟨1, h1⟩
  refine ⟨(ofMeasure μ f)⁻¹ • f, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hf]

/-- Tensor factorization uses the uniqueness of the algebraic Haar distribution on
one-variable tests and the finite tensor expansion of each product test. -/
theorem haarTensorFactorization (D : Distribution (G × Y)) :
    HaarTensorFactorizationStatement μ D := by
  classical
  intro hD
  obtain ⟨f₀, hf₀⟩ := exists_integralOneTest μ
  let S : Distribution Y := D.comp (SchwartzBruhat.tensorBilinear f₀)
  have hSingle (f : SchwartzBruhat G) (g : SchwartzBruhat Y) :
      D (SchwartzBruhat.tensor f g) = ofMeasure μ f * S g := by
    let T : Distribution G := D.comp (SchwartzBruhat.tensorBilinear.flip g)
    have hT : IsLeftInvariant T := by
      intro a
      rw [GroupAction.leftDistributions_eq_pushforward]
      ext b
      change D (SchwartzBruhat.tensor (pullback (Homeomorph.mulLeft a) b) g) = _
      have h : SchwartzBruhat.tensor (pullback (Homeomorph.mulLeft a) b) g =
          pullback ((Homeomorph.mulLeft a).prodCongr (Homeomorph.refl Y))
            (SchwartzBruhat.tensor b g) := rfl
      rw [h, ← pushforward_apply, hD a]
      rfl
    obtain ⟨c, hc, _⟩ := (RenardHaar.measureHaarBridge G μ).2.2 T hT
    have hCoeff : S g = c := by
      change T f₀ = c
      rw [hc, LinearMap.smul_apply, hf₀, smul_eq_mul, mul_one]
    change T f = _
    rw [hc, hCoeff, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨S, ?_, ?_⟩
  · ext f
    obtain ⟨n, a, b, hf⟩ := SchwartzBruhat.exists_tensor_expansion f
    have he : f = ∑ i, SchwartzBruhat.tensor (a i) (b i) := by
      ext ⟨x, y⟩
      simpa using hf x y
    rw [he, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [tensor_apply_tensor, hSingle]
  · intro S' hS'
    ext g
    change S' g = D (SchwartzBruhat.tensor f₀ g)
    rw [hS', tensor_apply_tensor, hf₀, one_mul]

variable [μ.IsMulRightInvariant]

/-- A right-translation symmetry accompanied by a homeomorphism of the second
factor induces a symmetry of the descended distribution. -/
theorem pushforward_eq_of_haarTensor_symmetry {D : Distribution (G × Y)} {S : Distribution Y}
    (hD : D = tensor (ofMeasure μ) S) (a : G) (e : Y ≃ₜ Y)
    (h : pushforward ((Homeomorph.mulRight a).prodCongr e) D = D) :
    pushforward e S = S := by
  obtain ⟨f₀, hf₀⟩ := exists_integralOneTest μ
  have hf₁ : ofMeasure μ (pullback (Homeomorph.mulRight a) f₀) = 1 := by
    rw [← hf₀, ofMeasure_apply, ofMeasure_apply]
    exact integral_mul_right_eq_self (μ := μ) (f₀ : G → ℂ) a
  rw [hD] at h
  ext g
  have hg := congrArg (fun E : Distribution (G × Y) => E (SchwartzBruhat.tensor f₀ g)) h
  rw [pushforward_apply, show pullback ((Homeomorph.mulRight a).prodCongr e)
    (SchwartzBruhat.tensor f₀ g) = SchwartzBruhat.tensor (pullback (Homeomorph.mulRight a) f₀)
      (pullback e g) from rfl,
    tensor_apply_tensor, tensor_apply_tensor, hf₁, hf₀, one_mul, one_mul] at hg
  exact hg

end Langlands.HarmonicAnalysis.Distribution
