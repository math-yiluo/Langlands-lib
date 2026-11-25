import Langlands.Analysis.DixmierMalliavin.Product
import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.InfiniteAdelicLinearRealization

/-!
# The Dixmier–Malliavin theorem for adelic test functions

`Langlands.Global.AdelicGroupPoints.IsAdelicTestFunction.exists_eq_sum_convolution`: for a connected
reductive group scheme `G` over a number field, every test function on `G(𝔸_F)` in the sense of
`IsAdelicTestFunction` (continuous, smooth infinite slices, compactly supported, invariant on the
right and on the left under open subgroups of `G(𝔸_f)`) is a finite sum of Haar convolutions of
compactly supported continuous test functions.

The proof transports `f` along `AdelicGroupPoints.split` to `G(F_∞) × G(𝔸_f)`, shrinks the right
invariance group to a compact open subgroup (`FiniteAdelicGroupPoints.compactOpenSubgroup`), and
applies `Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod` with the closed
linear realization of `G(F_∞)` of `InfiniteAdelicLinearRealization`; smooth slices are the
Library's plot-smooth slices by `reductive_isPlotSmooth_iff_contMDiff`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff CompactlySupported
open scoped Matrix.Norms.Operator

namespace Langlands.Global.AdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions InfiniteAdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- **Dixmier–Malliavin for the Library's test functions on `G(𝔸_F)`**, `G` connected reductive: every
`f` with `IsAdelicTestFunction F G f` is a finite sum of convolutions
`f(g) = ∑ᵢ ∫ φᵢ(a) ψᵢ(a⁻¹ g) da` (Haar measure of `G(𝔸_F)`) of compactly supported continuous
functions `φᵢ`, `ψᵢ` that are again test functions. -/
theorem IsAdelicTestFunction.exists_eq_sum_convolution
    (hG : GroupScheme.IsConnectedReductive G) {f : AdelicGroupPoints F G → ℂ}
    (hf : IsAdelicTestFunction F G f) :
    ∃ (n : ℕ) (φ ψ : Fin n → C_c(AdelicGroupPoints F G, ℂ)),
      (∀ i, IsAdelicTestFunction F G (φ i) ∧ IsAdelicTestFunction F G (ψ i)) ∧
      ∀ g, f g = ∑ i, ∫ a, φ i a * ψ i (a⁻¹ * g)
        ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := reductiveChartedSpace F G hG
  have := reductiveLieGroup F G hG
  obtain ⟨N, ρ, hρ⟩ := exists_isClosedLinearRealization F G hG
  let _ : MeasurableSpace (InfiniteAdelicGroupPoints F G) := borel _
  have : BorelSpace (InfiniteAdelicGroupPoints F G) := ⟨rfl⟩
  let _ : MeasurableSpace (FiniteAdelicGroupPoints F G) := borel _
  have : BorelSpace (FiniteAdelicGroupPoints F G) := ⟨rfl⟩
  set s := split F G
  set μG : Measure (AdelicGroupPoints F G) := Measure.haar
  have : (μG.map s).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μG s
  obtain ⟨⟨hcont, hslice, L, hLo, hLinv⟩, hfc, -⟩ := hf
  have hsliceiff : ∀ u : InfiniteAdelicGroupPoints F G → ℂ,
      u ∈ InfinitePlotSmoothFunctions F G ↔
        ContMDiff 𝓘(ℝ, smoothModel F hG.smoothDimension) 𝓘(ℝ, ℂ) ∞ u := fun u =>
    reductive_isPlotSmooth_iff_contMDiff F G hG u
  let f' : C_c(InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G, ℂ) :=
    ⟨⟨f ∘ s.symm, hcont.comp s.symm.continuous⟩, hfc.comp_homeomorph s.symm.toHomeomorph⟩
  have hf' : ∀ b, ContMDiff 𝓘(ℝ, smoothModel F hG.smoothDimension) 𝓘(ℝ, ℂ) ∞
      fun a => f' (a, b) := fun b => (hsliceiff _).1 (hslice b)
  set V : Subgroup (FiniteAdelicGroupPoints F G) :=
    L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup
  have hVo : IsOpen (V : Set (FiniteAdelicGroupPoints F G)) :=
    hLo.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hVc : IsCompact (V : Set (FiniteAdelicGroupPoints F G)) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      (V.isClosed_of_isOpen hVo) Set.inter_subset_right
  have hfV : ∀ x, ∀ v ∈ V, f' (x * (1, v)) = f' x := by
    intro x v hv
    change f (s.symm (x * (1, v))) = f (s.symm x)
    rw [map_mul]
    exact hLinv v hv.1 (s.symm x)
  obtain ⟨n, φ', ψ', hP, hsum⟩ :=
    Langlands.Analysis.DixmierMalliavin.exists_eq_sum_convolutionIntegral_prod hρ (μG.map s) f' hf'
      V hVo hVc hfV
  let lift : C_c(InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G, ℂ) →
      C_c(AdelicGroupPoints F G, ℂ) := fun u =>
    ⟨⟨u ∘ s, u.continuous.comp s.continuous⟩, u.hasCompactSupport.comp_homeomorph s.toHomeomorph⟩
  have hlift : ∀ u : C_c(InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G, ℂ),
      (∀ b, ContMDiff 𝓘(ℝ, smoothModel F hG.smoothDimension) 𝓘(ℝ, ℂ) ∞ fun a => u (a, b)) →
      (∀ x, ∀ v ∈ V, u (x * (1, v)) = u x) →
      (∃ V' : Subgroup (FiniteAdelicGroupPoints F G), IsOpen (V' : Set (FiniteAdelicGroupPoints F G)) ∧
        ∀ x, ∀ v ∈ V', u ((1, v) * x) = u x) →
      IsAdelicTestFunction F G (lift u) := by
    intro u hu hR ⟨V', hV'o, hV'⟩
    refine ⟨⟨(lift u).continuous, fun b => ?_, V, hVo, fun l hl g => ?_⟩,
      (lift u).hasCompactSupport, V', hV'o, fun l hl g => ?_⟩
    · rw [hsliceiff]
      have e : functionInfiniteSlice F G (lift u) b = fun a => u (a, b) := by
        funext a
        change u (s (s.symm (a, b))) = u (a, b)
        rw [ContinuousMulEquiv.apply_symm_apply]
      rw [e]
      exact hu b
    · change u (s (g * s.symm (1, l))) = u (s g)
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
      exact hR _ l hl
    · change u (s (s.symm (1, l) * g)) = u (s g)
      rw [map_mul, ContinuousMulEquiv.apply_symm_apply]
      exact hV' _ l hl
  refine ⟨n, fun i => lift (φ' i), fun i => lift (ψ' i), fun i => ⟨?_, ?_⟩, fun g => ?_⟩
  · obtain ⟨h1, -, h3, -, h5, -⟩ := hP i
    exact hlift _ h1 h3 h5
  · obtain ⟨-, h2, -, h4, -, h6⟩ := hP i
    exact hlift _ h2 h4 ⟨V, hVo, h6⟩
  · have hg : f g = f' (s g) := by
      change f g = f (s.symm (s g))
      rw [ContinuousMulEquiv.symm_apply_apply]
    rw [hg, hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Hecke.convolutionIntegral_comp_continuousMulEquiv s μG (φ' i) (ψ' i) g
    rw [Hecke.convolutionIntegral, Hecke.convolutionIntegral] at this
    exact this.symm

end Langlands.Global.AdelicGroupPoints
