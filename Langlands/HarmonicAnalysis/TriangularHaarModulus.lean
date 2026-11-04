import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
import Langlands.HarmonicAnalysis.TriangularTranslationProof

/-!
# Haar modulus in triangular coordinates

A group homeomorphic to `Fin d → A` whose left translations are triangular shears carries
the transported product Haar measure as a left Haar measure; an automorphism acting
diagonally in these coordinates has Haar modulus equal to the product of the
coordinatewise moduli. The paired Markdown records the argument.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis

section Characterization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar modulus is the unique scalar `c` with `c • φ_* μ = μ` for one regular Haar
measure `μ`. -/
@[to_additive addEquivAddHaarChar_eq_of_smul_map
/-- The additive Haar modulus is the unique scalar `c` with `c • φ_* μ = μ`
for one regular additive Haar measure `μ`. -/]
theorem mulEquivHaarChar_eq_of_smul_map (μ : Measure G) [IsHaarMeasure μ] [Regular μ]
    (φ : G ≃ₜ* G) {c : ℝ≥0} (h : c • μ.map φ = μ) :
    mulEquivHaarChar φ = c := by
  have : IsHaarMeasure (μ.map φ) := φ.isHaarMeasure_map μ
  rw [mulEquivHaarChar_eq μ φ]
  have hs := haarScalarFactor_smul (μ.map φ) (μ.map φ) (c := c)
  rw! [h] at hs
  simpa using hs

end Characterization

section Shear

variable {A : Type*} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd₂ A] [MeasurableSub₂ A]

/-- A self-map of `Fin d → A` is a triangular shear when each output coordinate differs
from the input coordinate by an amount depending only on the earlier input coordinates. -/
def IsTriangularShear {d : ℕ} (f : (Fin d → A) → Fin d → A) : Prop :=
  ∀ (k : Fin d) (v w : Fin d → A), (∀ l < k, v l = w l) → f v k - v k = f w k - w k

variable (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant]

/-- Measurable triangular shears preserve the product of a translation-invariant
σ-finite measure. This is the Library's `finiteTriangularTranslation` with the coordinate
index as rank. -/
theorem measurePreserving_of_isTriangularShear {d : ℕ} (f : (Fin d → A) → Fin d → A)
    (hf : Measurable f) (htri : IsTriangularShear f) :
    MeasurePreserving f (Measure.pi fun _ : Fin d => ν) (Measure.pi fun _ : Fin d => ν) := by
  have h := finiteTriangularTranslation (Fin d) (fun _ => A) (fun _ => ν) (fun k => (k : ℕ))
    (fun v k => f v k - v k) (hf.sub measurable_id)
    (fun k v w hvw => htri k v w fun l hl => hvw l hl)
  simpa only [sub_add_cancel] using h

end Shear

section Modulus

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  {A : Type*} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

/-- **Haar modulus in triangular coordinates.** Let `Φ : H ≃ₜ (Fin d → A)` be coordinates in
which every left translation of `H` is a triangular shear, and let `ψ` act on the `k`-th
coordinate by a measurable map `s k` with `r k • (s k)_* ν = ν` for an additive Haar measure
`ν` on `A`. Then the Haar modulus of `ψ` is `∏ k, r k`. -/
theorem mulEquivHaarChar_eq_prod_of_triangular (ν : Measure A) [IsAddHaarMeasure ν]
    {d : ℕ} (Φ : H ≃ₜ (Fin d → A))
    (htri : ∀ g : H, IsTriangularShear fun v => Φ (g * Φ.symm v))
    (ψ : H ≃ₜ* H) (s : Fin d → A → A) (hs : ∀ k, Measurable (s k))
    (r : Fin d → ℝ≥0) (hr : ∀ k, r k • ν.map (s k) = ν)
    (hψ : ∀ h k, Φ (ψ h) k = s k (Φ h k)) :
    mulEquivHaarChar ψ = ∏ k, r k := by
  have hΦ : Measurable Φ := Φ.continuous.measurable
  have hΦs : Measurable Φ.symm := Φ.symm.continuous.measurable
  have hψm : Measurable ψ := ψ.continuous.measurable
  let π : Measure (Fin d → A) := Measure.pi fun _ => ν
  let μ : Measure H := π.map Φ.symm
  -- left invariance from the shear lemma
  have hinv : IsMulLeftInvariant μ := by
    constructor
    intro g
    have hS : MeasurePreserving (fun v => Φ (g * Φ.symm v)) π π :=
      measurePreserving_of_isTriangularShear ν _
        (hΦ.comp ((measurable_const_mul g).comp hΦs)) (htri g)
    have hcomp : (fun x => g * x) ∘ Φ.symm = Φ.symm ∘ fun v => Φ (g * Φ.symm v) := by
      funext v; simp
    change Measure.map (fun x => g * x) (π.map Φ.symm) = π.map Φ.symm
    rw [Measure.map_map (measurable_const_mul g) hΦs, hcomp,
      ← Measure.map_map hΦs hS.measurable, hS.map_eq]
  have hfin : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.map π Φ.symm
  have hopen : IsOpenPosMeasure μ := Φ.symm.continuous.isOpenPosMeasure_map Φ.symm.surjective
  have hHaar : IsHaarMeasure μ := { }
  have : SecondCountableTopology H := Φ.isEmbedding.secondCountableTopology
  have hreg : Regular μ := by
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts H) := inferInstance
    exact regular_of_isMulLeftInvariant K.isCompact K.interior_nonempty
      K.isCompact.measure_lt_top.ne
  -- the coordinatewise scalings
  have hν0 : ν ≠ 0 := NeZero.ne ν
  have hr0 : ∀ k, r k ≠ 0 := by
    intro k hk
    apply hν0
    rw [← hr k, hk, zero_smul]
  have hmap : ∀ k, ν.map (s k) = (r k)⁻¹ • ν := by
    intro k
    conv_rhs => rw [← hr k]
    rw [smul_smul, inv_mul_cancel₀ (hr0 k), one_smul]
  have hpi : π.map (fun v k => s k (v k)) = (∏ k, r k)⁻¹ • π := by
    have : ∀ k, SigmaFinite (ν.map (s k)) := fun k => by rw [hmap k]; infer_instance
    rw [Measure.pi_map_pi (fun k => (hs k).aemeasurable)]
    simp_rw [hmap]
    rw [pi_nnreal_smul, ← Finset.prod_inv_distrib]
  have hψcoord : ψ ∘ Φ.symm = Φ.symm ∘ fun v k => s k (v k) := by
    funext v
    apply Φ.injective
    funext k
    simp [hψ]
  apply mulEquivHaarChar_eq_of_smul_map μ ψ
  change (∏ k, r k) • Measure.map ψ (π.map Φ.symm) = π.map Φ.symm
  have hsm : Measurable fun (v : Fin d → A) k => s k (v k) :=
    measurable_pi_iff.mpr fun k => (hs k).comp (measurable_pi_apply k)
  rw [Measure.map_map hψm hΦs, hψcoord, ← Measure.map_map hΦs hsm, hpi,
    Measure.map_smul _ hΦs.aemeasurable, smul_smul, mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hr0 k),
    one_smul]

end Modulus

end Langlands.HarmonicAnalysis
