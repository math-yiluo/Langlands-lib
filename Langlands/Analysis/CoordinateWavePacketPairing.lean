import Langlands.Analysis.CoordinatePartialPlancherel
import Langlands.Analysis.SquareIntegrableFibrePairing

/-! # Pairing after Fourier integration in a common coordinate -/

noncomputable section

set_option autoImplicit false

open Filter MeasureTheory
open scoped ENNReal

namespace Langlands.Analysis

private theorem measurePreserving_swapFirst {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (a : Measure A) (b : Measure B) (c : Measure C) [SFinite a] [SFinite b] [SFinite c] :
    MeasurePreserving (fun p : A × (B × C) => (p.2.1, (p.1, p.2.2)))
      (a.prod (b.prod c)) (b.prod (a.prod c)) :=
  (measurePreserving_prodAssoc b a c).comp
    (((Measure.measurePreserving_swap (μ := a) (ν := b)).prod (MeasurePreserving.id c)).comp
      ((measurePreserving_prodAssoc a b c).symm (e := MeasurableEquiv.prodAssoc)))

private theorem ae_memLp_two_prodMk_left {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {a : Measure A} {b : Measure B} [SFinite a] [SFinite b] {f : A × B → ℂ}
    (hf : MemLp f 2 (a.prod b)) : ∀ᵐ x ∂a, MemLp (fun y => f (x, y)) 2 b := by
  have hsq := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  filter_upwards [hf.aestronglyMeasurable.prodMk_left, hsq.prod_right_ae] with x hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hi

variable {m : ℕ} {U V Q : Type*} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace Q]

local notation "Z[" n "]" => (Fin n → ℝ)
local notation "ζ[" n "]" => (volume : Measure (Fin n → ℝ))

private theorem ae_integrable_frequency
    {μ : Measure Q} [SFinite μ] {s : Set Z[m]} (hfin : ζ[m] s < ∞) {f : Z[m] × Q → ℂ}
    (hf : MemLp f 2 ((ζ[m]).prod μ)) (hs : ∀ z ∉ s, ∀ q, f (z, q) = 0) :
    ∀ᵐ q ∂μ, Integrable (fun z => f (z, q)) ζ[m] := by
  let : Fact (ζ[m] s < ∞) := ⟨hfin⟩
  have hswap := Measure.measurePreserving_swap (μ := μ) (ν := ζ[m])
  filter_upwards [ae_memLp_two_prodMk_left (hf.comp_measurePreserving hswap)] with q hq
  have hq₁ : IntegrableOn (fun z => f (z, q)) s ζ[m] :=
    (hq.restrict s).integrable (by norm_num)
  exact hq₁.integrable_of_forall_notMem_eq_zero (fun z hz => hs z hz q)

/-- Integrate the noncentral frequency and take the positive-phase Fourier integral
in the remaining frequency, leaving the common measured variable fixed. -/
def coordinateWavePacket (α : Measure U) (f : U × (Z[m] × Q) → ℂ) : Z[m] × Q → ℂ :=
  coordinatePartialFourier (fun p => ∫ u, f (u, p) ∂α)

/-- Finite noncentral frequency measures and finite central frequency support allow
Plancherel and Fubini to express the pairing using the same central frequency on both sides. -/
def CoordinateWavePacketPairingStatement : Prop :=
  ∀ {m : ℕ} {U V Q : Type*} [MeasurableSpace U] [MeasurableSpace V] [MeasurableSpace Q]
    (α : Measure U) (β : Measure V) (μ : Measure Q)
    [IsFiniteMeasure α] [IsFiniteMeasure β] [SFinite μ]
    (f : U × (Z[m] × Q) → ℂ) (g : V × (Z[m] × Q) → ℂ) (s t : Set Z[m]),
    ζ[m] s < ∞ → ζ[m] t < ∞ →
    MemLp f 2 (α.prod ((ζ[m]).prod μ)) → MemLp g 2 (β.prod ((ζ[m]).prod μ)) →
    (∀ z ∉ s, ∀ u q, f (u, (z, q)) = 0) → (∀ z ∉ t, ∀ v q, g (v, (z, q)) = 0) →
    MemLp (coordinateWavePacket α f) 2 ((ζ[m]).prod μ) ∧
    MemLp (coordinateWavePacket β g) 2 ((ζ[m]).prod μ) ∧
    Integrable (fun p : Z[m] × (U × V) =>
      ∫ q, f (p.2.1, (p.1, q)) * (starRingEnd ℂ) (g (p.2.2, (p.1, q))) ∂μ)
      ((ζ[m]).prod (α.prod β)) ∧
    (∫ p, coordinateWavePacket α f p * (starRingEnd ℂ) (coordinateWavePacket β g p)
      ∂((ζ[m]).prod μ)) =
      ((2 * Real.pi : ℝ) ^ m : ℂ) *
        ∫ z, ∫ u, ∫ v, ∫ q, f (u, (z, q)) * (starRingEnd ℂ) (g (v, (z, q))) ∂μ ∂β ∂α ∂ζ[m]

/-- Apply partial Plancherel to the integrated families and Fubini to the pairing. -/
theorem coordinateWavePacketPairing : CoordinateWavePacketPairingStatement := by
  intro m U V Q _ _ _ α β μ _ _ _ f g s t hs ht hf hg hfs hgt
  let F (p : Z[m] × Q) : ℂ := ∫ u, f (u, p) ∂α
  let G (p : Z[m] × Q) : ℂ := ∫ v, g (v, p) ∂β
  have hF : MemLp F 2 ((ζ[m]).prod μ) := memLp_two_integral_fst hf
  have hG : MemLp G 2 ((ζ[m]).prod μ) := memLp_two_integral_fst hg
  have hFs : ∀ z ∉ s, ∀ q, F (z, q) = 0 := by
    intro z hz q
    simp [F, hfs z hz]
  have hGt : ∀ z ∉ t, ∀ q, G (z, q) = 0 := by
    intro z hz q
    simp [G, hgt z hz]
  obtain ⟨hPF, hPG, hpl⟩ := coordinatePartialPlancherel μ F G hF hG
    (ae_integrable_frequency hs hF hFs) (ae_integrable_frequency ht hG hGt)
  have hfz : MemLp (fun p : Z[m] × (U × Q) => f (p.2.1, (p.1, p.2.2))) 2
      ((ζ[m]).prod (α.prod μ)) := hf.comp_measurePreserving (measurePreserving_swapFirst ζ[m] α μ)
  have hgz : MemLp (fun p : Z[m] × (V × Q) => g (p.2.1, (p.1, p.2.2))) 2
      ((ζ[m]).prod (β.prod μ)) := hg.comp_measurePreserving (measurePreserving_swapFirst ζ[m] β μ)
  have hassoc := ((MeasurePreserving.id ζ[m]).prod (measurePreserving_prodAssoc α β μ)).comp
    (measurePreserving_prodAssoc ζ[m] (α.prod β) μ)
  have hfun : MemLp (fun p : (Z[m] × (U × V)) × Q => f (p.1.2.1, (p.1.1, p.2))) 2
      (((ζ[m]).prod (α.prod β)).prod μ) :=
    (hfz.comp_snd β).comp_measurePreserving
      ((measurePreserving_swapFirst ζ[m] β (α.prod μ)).comp
        (((MeasurePreserving.id ζ[m]).prod (measurePreserving_swapFirst α β μ)).comp hassoc))
  have hgun : MemLp (fun p : (Z[m] × (U × V)) × Q => g (p.1.2.2, (p.1.1, p.2))) 2
      (((ζ[m]).prod (α.prod β)).prod μ) :=
    (hgz.comp_snd α).comp_measurePreserving
      ((measurePreserving_swapFirst ζ[m] α (β.prod μ)).comp hassoc)
  have hprod : Integrable (fun p : (Z[m] × (U × V)) × Q =>
      f (p.1.2.1, (p.1.1, p.2)) * (starRingEnd ℂ) (g (p.1.2.2, (p.1.1, p.2))))
      (((ζ[m]).prod (α.prod β)).prod μ) := hfun.integrable_mul hgun.star
  refine ⟨hPF, hPG, hprod.integral_prod_left, hpl.trans ?_⟩
  congr 1
  have hFG : Integrable (fun p => F p * (starRingEnd ℂ) (G p)) ((ζ[m]).prod μ) :=
    hF.integrable_mul hG.star
  rw [integral_prod _ hFG]
  apply integral_congr_ae
  filter_upwards [ae_memLp_two_prodMk_left hfz, ae_memLp_two_prodMk_left hgz] with z hzf hzg
  exact (squareIntegrableFibrePairing α β μ (fun p => f (p.1, (z, p.2)))
    (fun p => g (p.1, (z, p.2))) hzf hzg).2

end Langlands.Analysis
