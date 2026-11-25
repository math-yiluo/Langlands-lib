import Langlands.HarmonicAnalysis.Bicharacter.Fourier
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Gauss integrals and Weil's formula

A function `f` on `X` has *Gauss integral* `γ` for the measure `μ` (`HasGaussIntegral μ f γ`) if
every compact set lies in a compact open subgroup `L` with `∫_L f dμ = γ`, so that the integrals
of `f` over large compact open subgroups stabilize at `γ`. For a character of second degree `f`
this is the regularized integral of A. Weil, *Sur certains groupes d'opérateurs unitaires*,
Acta Math. 111 (1964), chapter II, n° 27, pp. 174–175 (for a non-degenerate quadratic form `f`
over a local field with discrete valuation, `∫_M χ(f(x)) dx` does not depend on the lattice `M`
once `M` is large, and `γ(f)` is the argument of that value).

Weil's formula (`bicharacterFourier_mul_bicharacterFourier`): if `f y e(y, u) = g(u) f(y + s(u))`
for all `y`, `u` (for a character of second degree `f(y) = ψ(½ Q(y))` with `Q(y, u) = e`-pairing,
`s` is the inverse of the associated map and `g = f⁻¹ ∘ s`) and `f` has Gauss integral `γ`, then

`ℱ (f · ℱ φ) (x) = γ ∫ g(x + z) φ(z) dz`

for every Schwartz–Bruhat function `φ`. Gauss integrals are transported along additive
homeomorphisms that scale the measures (`HasGaussIntegral.comp_addEquiv`) and multiply over finite
products (`HasGaussIntegral.pi`).
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Langlands.HarmonicAnalysis

variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X]

/-- `f` has Gauss integral `γ` for `μ`: every compact set lies in a compact open subgroup `L`
with `∫_L f dμ = γ`. -/
def HasGaussIntegral (μ : Measure X) (f : X → ℂ) (γ : ℂ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧
    K ⊆ L ∧ ∫ x in (L : Set X), f x ∂μ = γ

namespace GaussIntegral.Internal

theorem setIntegral_addSubgroup_add_right [IsTopologicalAddGroup X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (L : AddSubgroup X) (hLo : IsOpen (L : Set X))
    (g : X → ℂ) {t : X} (ht : t ∈ L) :
    ∫ z in (L : Set X), g (z + t) ∂μ = ∫ z in (L : Set X), g z ∂μ := by
  simp_rw [add_comm _ t]
  rw [← integral_indicator hLo.measurableSet, ← integral_indicator hLo.measurableSet,
    ← integral_add_left_eq_self (μ := μ) ((L : Set X).indicator g) t]
  congr 1
  funext z
  by_cases hz : z ∈ L
  · rw [Set.indicator_of_mem (show z ∈ (L : Set X) from hz),
      Set.indicator_of_mem (show t + z ∈ (L : Set X) from L.add_mem ht hz)]
  · have hz' : t + z ∉ L := fun h => hz ((L.add_mem_cancel_left ht).1 h)
    rw [Set.indicator_of_notMem (show z ∉ (L : Set X) from hz),
      Set.indicator_of_notMem (show t + z ∉ (L : Set X) from hz')]

end GaussIntegral.Internal

open GaussIntegral.Internal

/-- **Weil's formula** for the Fourier transform of a function times a character of second
degree. -/
theorem bicharacterFourier_mul_bicharacterFourier [IsTopologicalAddGroup X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] (μ : Measure X)
    [μ.IsAddHaarMeasure] {e : X → X → ℂ} (he : IsSelfDualBicharacter e) {f g : X → ℂ}
    {s : X → X} {γ : ℂ} (hf : Continuous f) (hs : Continuous s)
    (hfg : ∀ y u, f y * e y u = g u * f (y + s u)) (hga : HasGaussIntegral μ f γ)
    {φ : X → ℂ} (hφ : φ ∈ schwartzBruhatSubmodule X) (x : X) :
    bicharacterFourier μ e (fun y => f y * bicharacterFourier μ e φ y) x =
      γ * ∫ z, g (x + z) * φ z ∂μ := by
  have hφ4 : bicharacterFourier μ e φ ∈ schwartzBruhatSubmodule X :=
    bicharacterFourier_mem μ he hφ
  have hK1 : IsCompact (tsupport (bicharacterFourier μ e φ)) := hφ4.2
  have hφc : IsCompact (tsupport φ) := hφ.2
  have hK2 : IsCompact (s '' ((fun z => x + z) '' tsupport φ)) :=
    (hφc.image (continuous_const.add continuous_id)).image hs
  obtain ⟨L, hLc, hLo, hKL, hLγ⟩ := hga _ (hK1.union hK2)
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have he_cont : Continuous (fun p : X × X => e p.1 p.2) := he.continuous
  have hφcont : Continuous φ := hφ.1.continuous
  have h0 : ∀ y, y ∉ (L : Set X) → e x y * (f y * bicharacterFourier μ e φ y) = 0 := by
    intro y hy
    have : bicharacterFourier μ e φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy (hKL (Or.inl h)))
    simp [this]
  have h1 : bicharacterFourier μ e (fun y => f y * bicharacterFourier μ e φ y) x
      = ∫ y in (L : Set X), ∫ z, e x y * f y * (e y z * φ z) ∂μ ∂μ := by
    calc bicharacterFourier μ e (fun y => f y * bicharacterFourier μ e φ y) x
        = ∫ y, e x y * (f y * bicharacterFourier μ e φ y) ∂μ := rfl
      _ = ∫ y in (L : Set X), e x y * (f y * bicharacterFourier μ e φ y) ∂μ :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero h0).symm
      _ = _ := by
          congr 1; funext y
          simp only [bicharacterFourier]
          rw [← mul_assoc, ← integral_const_mul]
  have hint : Integrable (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
      ((μ.restrict (L : Set X)).prod μ) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hc : Continuous (Function.uncurry fun y z => e x y * f y * (e y z * φ z)) := by
      have h1' : Continuous fun p : X × X => e x p.1 :=
        he_cont.comp (continuous_const.prodMk continuous_fst)
      exact (h1'.mul (hf.comp continuous_fst)).mul (he_cont.mul (hφcont.comp continuous_snd))
    have hon : IntegrableOn (Function.uncurry fun y z => e x y * f y * (e y z * φ z))
        ((L : Set X) ×ˢ tsupport φ) (μ.prod μ) :=
      hc.continuousOn.integrableOn_compact (hLc.prod hφc)
    refine hon.of_forall_sdiff_eq_zero (hLm.prod MeasurableSet.univ) ?_
    rintro ⟨y, z⟩ ⟨⟨hy, -⟩, hn⟩
    have hz : z ∉ tsupport φ := fun h => hn ⟨hy, h⟩
    simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  have h3 : ∀ z, ∫ y in (L : Set X), e x y * f y * (e y z * φ z) ∂μ =
      γ * (g (x + z) * φ z) := by
    intro z
    by_cases hz : φ z = 0
    · simp [hz]
    · have hzt : z ∈ tsupport φ := subset_tsupport _ hz
      have hsL : s (x + z) ∈ L := hKL (Or.inr ⟨x + z, ⟨z, hzt, rfl⟩, rfl⟩)
      have hpt : ∀ y, e x y * f y * (e y z * φ z) = φ z * g (x + z) * f (y + s (x + z)) := by
        intro y
        have hexy : e x y * e y z = e y (x + z) := by
          rw [he.symm y (x + z), he.map_add_left, he.symm z y]
        rw [mul_assoc (φ z), ← hfg y (x + z), ← hexy]; ring
      simp_rw [hpt]
      rw [integral_const_mul, setIntegral_addSubgroup_add_right μ L hLo f hsL, hLγ]; ring
  rw [h1, integral_integral_swap hint]
  simp_rw [h3]
  rw [integral_const_mul]

/-- Gauss integrals along an additive homeomorphism that scales the measures. -/
theorem HasGaussIntegral.comp_addEquiv {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] {μ : Measure X} {μ' : Measure Y}
    (T : X ≃ₜ+ Y) {r : NNReal} {f : Y → ℂ} {γ : ℂ} (hμ : μ.map T = r • μ')
    (h : HasGaussIntegral μ' f γ) : HasGaussIntegral μ (fun x => f (T x)) ((r : ℝ) * γ) := by
  intro K hK
  obtain ⟨L, hLc, hLo, hKL, hint⟩ := h (T '' K) (hK.image T.continuous)
  have hme : MeasurableEmbedding (T : X → Y) := T.toHomeomorph.measurableEmbedding
  have hset : ((L.comap (T.toAddEquiv.toAddMonoidHom) : AddSubgroup X) : Set X) =
      (T : X → Y) ⁻¹' (L : Set Y) := rfl
  refine ⟨L.comap T.toAddEquiv.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [hset]
    exact T.toHomeomorph.isCompact_preimage.2 hLc
  · rw [hset]
    exact hLo.preimage T.continuous
  · rw [hset]
    intro x hx
    exact hKL ⟨x, hx, rfl⟩
  · rw [hset, ← hme.setIntegral_map f (L : Set Y), hμ, Measure.restrict_smul,
      integral_smul_nnreal_measure, hint]
    simp [NNReal.smul_def]

/-- Gauss integrals of products of functions of the coordinates, for a product measure. -/
theorem HasGaussIntegral.pi {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [LocallyCompactSpace Y] [SecondCountableTopology Y] [T2Space Y]
    {μ : Measure Y} [μ.IsAddHaarMeasure] {ι : Type*} [Fintype ι] {f : ι → Y → ℂ} {γ : ι → ℂ}
    (hf : ∀ i, HasGaussIntegral μ (f i) (γ i)) :
    HasGaussIntegral (Measure.pi fun _ : ι => μ) (fun x => ∏ i, f i (x i)) (∏ i, γ i) := by
  intro K hK
  have : SigmaFinite μ := sigmaFinite_of_locallyFinite
  have hL : ∀ i, ∃ L : AddSubgroup Y, IsCompact (L : Set Y) ∧ IsOpen (L : Set Y) ∧
      (Function.eval i '' K) ⊆ L ∧ ∫ x in (L : Set Y), f i x ∂μ = γ i :=
    fun i => hf i _ (hK.image (continuous_apply i))
  choose L hLc hLo hLK hLi using hL
  refine ⟨AddSubgroup.pi Set.univ L, ?_, ?_, ?_, ?_⟩
  · rw [AddSubgroup.coe_pi]; exact isCompact_univ_pi hLc
  · rw [AddSubgroup.coe_pi]; exact isOpen_set_pi Set.finite_univ fun i _ => hLo i
  · intro x hx
    rw [SetLike.mem_coe, AddSubgroup.mem_pi]
    intro i _
    exact hLK i ⟨x, hx, rfl⟩
  · rw [AddSubgroup.coe_pi, Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
    exact Finset.prod_congr rfl fun i _ => hLi i

end Langlands.HarmonicAnalysis
