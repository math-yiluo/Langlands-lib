import Langlands.Global.AdelicTemperedComponentInputs
import Langlands.Global.InfiniteAdelicLinearRealization
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Global.FiniteAdelicGroupCompactOpen
import Langlands.Global.AdelicGroupPolish
import Langlands.Representation.Archimedean.LinearRealizationParametrix

/-! # Proof of the local Sobolev identity on `G(𝔸)`

`Langlands.Global.adelicSmoothVectorParametrix` proves `AdelicSmoothVectorParametrixStatement`.
The auxiliary results are a closed linear realization of `G(F_∞)` for the atlas
`smoothChartedSpace F G hsmooth`, the left Haar measure `infiniteSliceMeasure V` on `G(F_∞)` (the
image under the infinite projection of the Haar measure of `G(𝔸)` restricted to the points whose
finite part lies in a compact open subgroup `V`), and the rewriting of integrals over `G(𝔸)` against
`κ(g_∞) 1_V(g_f)` as integrals over `G(F_∞)` against `infiniteSliceMeasure V`
(`integral_indicator_smul_eq`). -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global

namespace InfiniteAdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left]

/-- For connected reductive `G`, `G(F_∞)` with the atlas `smoothChartedSpace F G hsmooth` has a
closed linear realization. -/
theorem exists_isClosedLinearRealization_of_smooth (hG : GroupScheme.IsConnectedReductive G)
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∃ (N : ℕ) (ρ : InfiniteAdelicGroupPoints F G →* (ArchimedeanMatrix F N)ˣ),
      LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, smoothModel F d) ρ := by
  obtain ⟨N, ρ, hρ, -⟩ := InfinitePlaceGroupPoints.exists_closedMatrixRealization G hG
  exact ⟨N, matrixRealization F G ρ,
    isClosedLinearRealization_matrixRealization_of_smooth F G hsmooth ρ hρ⟩

end InfiniteAdelicGroupPoints

namespace AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- Every adelic point is the product of its infinite and finite parts. -/
theorem ofInfinite_infinite_mul_ofFinite_finite (g : AdelicGroupPoints F G) :
    ofInfinite F G (infinite F G g) * ofFinite F G (finite F G g) = g := by
  rw [ofInfinite_eq_pair, ofFinite_eq_pair, pair_mul, mul_one, one_mul, pair_projections]

/-- The image under the infinite projection of the Haar measure of `G(𝔸)` restricted to the
points whose finite part lies in `V`. -/
def infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G)) :
    Measure (InfiniteAdelicGroupPoints F G) :=
  Measure.map (infinite F G)
    ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict (finite F G ⁻¹' V))

omit [LocallyOfFiniteType G.X.hom] in
theorem measurable_infinite : Measurable (infinite F G) := (infinite F G).continuous.measurable

/-- For a compact open subgroup `V` of `G(𝔸_f)`, `infiniteSliceMeasure V` is a left Haar measure
on `G(F_∞)`. -/
theorem isHaarMeasure_infiniteSliceMeasure {V : Subgroup (FiniteAdelicGroupPoints F G)}
    (hVo : IsOpen (V : Set (FiniteAdelicGroupPoints F G)))
    (hVc : IsCompact (V : Set (FiniteAdelicGroupPoints F G))) :
    (infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G))).IsHaarMeasure := by
  set S := finite F G ⁻¹' (V : Set (FiniteAdelicGroupPoints F G)) with hSdef
  have hSo : IsOpen S := hVo.preimage (finite F G).continuous
  have hS : MeasurableSet S := hSo.measurableSet
  have hinf := measurable_infinite (F := F) (G := G)
  have h1 : IsFiniteMeasureOnCompacts
      (infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G))) := by
    refine ⟨fun K hK => ?_⟩
    rw [infiniteSliceMeasure, Measure.map_apply hinf hK.isClosed.measurableSet,
      Measure.restrict_apply' hS]
    have he : infinite F G ⁻¹' K ∩ S = split F G ⁻¹' (K ×ˢ (V : Set _)) := by
      ext g; simp [S, split_apply]
    rw [he]
    exact ((split F G).toHomeomorph.isCompact_preimage.2 (hK.prod hVc)).measure_lt_top
  have h2 : (infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G))).IsMulLeftInvariant := by
    refine ⟨fun x => ?_⟩
    rw [infiniteSliceMeasure, Measure.map_map (measurable_const_mul x) hinf]
    have hcomm : (fun g => x * g) ∘ infinite F G =
        infinite F G ∘ (fun g => ofInfinite F G x * g) := by
      funext g; simp [map_mul]
    rw [hcomm, ← Measure.map_map hinf (measurable_const_mul _)]
    congr 1
    let e := MeasurableEquiv.mulLeft (ofInfinite F G x)
    have hpre : e ⁻¹' S = S := by
      ext g; simp [e, S, map_mul]
    have h := MeasurableEquiv.restrict_map e
      (Measure.haar : Measure (AdelicGroupPoints F G)) S
    rw [hpre, MeasurableEquiv.coe_mulLeft, map_mul_left_eq_self] at h
    exact h.symm
  have h3 : (infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G))).IsOpenPosMeasure := by
    refine ⟨fun U hU hne => ?_⟩
    rw [infiniteSliceMeasure, Measure.map_apply hinf hU.measurableSet,
      Measure.restrict_apply' hS]
    obtain ⟨u, hu⟩ := hne
    exact ((hU.preimage (infinite F G).continuous).inter hSo).measure_ne_zero
      (Measure.haar : Measure (AdelicGroupPoints F G))
      ⟨ofInfinite F G u, by simpa using hu, by simp [S, V.one_mem]⟩
  exact @Measure.IsHaarMeasure.mk _ _ _ _ _ h1 h2 h3

/-- Integration against `κ(g_∞) 1_V(g_f)` on `G(𝔸)` of the orbit of a vector fixed by `ρ(V)` is
integration over `G(F_∞)` against `infiniteSliceMeasure V`. -/
theorem integral_indicator_smul_eq {V : Subgroup (FiniteAdelicGroupPoints F G)}
    (hVo : IsOpen (V : Set (FiniteAdelicGroupPoints F G)))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ρ : AdelicGroupPoints F G →* (E →L[ℂ] E))
    (hρ : Langlands.Archimedean.IsContinuousRepresentation ρ)
    {κ : InfiniteAdelicGroupPoints F G → ℂ} (hκ : Continuous κ) (u : E)
    (hu : ∀ l ∈ V, ρ (ofFinite F G l) u = u) :
    ∫ g, (κ (infinite F G g) *
        (finite F G ⁻¹' (V : Set (FiniteAdelicGroupPoints F G))).indicator 1 g) • ρ g u
        ∂(Measure.haar : Measure (AdelicGroupPoints F G)) =
      ∫ x, κ x • ρ (ofInfinite F G x) u ∂infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G)) := by
  set S := finite F G ⁻¹' (V : Set (FiniteAdelicGroupPoints F G)) with hSdef
  have hS : MeasurableSet S := (hVo.preimage (finite F G).continuous).measurableSet
  have hpt : ∀ g, (κ (infinite F G g) * S.indicator 1 g) • ρ g u =
      S.indicator (fun g => κ (infinite F G g) • ρ (ofInfinite F G (infinite F G g)) u) g := by
    intro g
    by_cases hg : g ∈ S
    · rw [indicator_of_mem hg, indicator_of_mem hg, Pi.one_apply, mul_one]
      congr 1
      conv_lhs => rw [← ofInfinite_infinite_mul_ofFinite_finite g]
      rw [map_mul, mul_apply_eq_comp, hu _ hg]
    · rw [indicator_of_notMem hg, indicator_of_notMem hg, mul_zero, zero_smul]
  simp_rw [hpt]
  rw [integral_indicator hS]
  have hc : Continuous fun x => κ x • ρ (ofInfinite F G x) u :=
    hκ.smul (hρ.comp ((ofInfinite F G).continuous.prodMk continuous_const))
  rw [infiniteSliceMeasure, integral_map measurable_infinite.aemeasurable hc.aestronglyMeasurable]

end AdelicGroupPoints

open GroupScheme AdelicGroupPoints Langlands.Archimedean in
/-- **The local Sobolev identity on `G(𝔸)`** (`AdelicSmoothVectorParametrixStatement`). For an open
subgroup `L` of `G(𝔸_f)` put `V = L ∩ K_f` with `K_f` a compact open subgroup and
`μ_∞ = infiniteSliceMeasure V`, a Haar measure on `G(F_∞)`. The identity on Lie groups with a closed
linear realization (`exists_sum_integral_iteratedLieDerivative`) gives words `wordⱼ` and functions
`κⱼ` on `G(F_∞)`; the functions `φ'ⱼ(g) = κⱼ(g_∞) 1_V(g_f)` turn its integrals into integrals over
`G(𝔸)` (`integral_indicator_smul_eq`, using that `ρ(V)` fixes the derivatives of `v`), and the
`φ'ⱼ` with equal words are added up. -/
theorem adelicSmoothVectorParametrix : AdelicSmoothVectorParametrixStatement := by
  intro F _ _ G _ _ _ hG d hsmooth L hL
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  have hLie : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (InfiniteAdelicGroupPoints F G) := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  obtain ⟨N, ρL, hρL⟩ :=
    InfiniteAdelicGroupPoints.exists_isClosedLinearRealization_of_smooth F G hG hsmooth
  set V : Subgroup (FiniteAdelicGroupPoints F G) :=
    L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup with hVdef
  have hVo : IsOpen (V : Set (FiniteAdelicGroupPoints F G)) :=
    hL.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hVc : IsCompact (V : Set (FiniteAdelicGroupPoints F G)) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      (V.isClosed_of_isOpen hVo) Set.inter_subset_right
  have hHaar := isHaarMeasure_infiniteSliceMeasure hVo hVc
  obtain ⟨M, word, κ, hκ, hid⟩ :=
    exists_sum_integral_iteratedLieDerivative.{_, _, 0, _} hρL
      (infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G)))
  set S : Set (AdelicGroupPoints F G) :=
    finite F G ⁻¹' (V : Set (FiniteAdelicGroupPoints F G)) with hSdef
  have hSc : IsClopen S := ⟨(V.isClosed_of_isOpen hVo).preimage (finite F G).continuous,
    hVo.preimage (finite F G).continuous⟩
  let φ' : Fin M → AdelicGroupPoints F G → ℂ := fun j g => κ j (infinite F G g) * S.indicator 1 g
  have hφ'c : ∀ j, Continuous (φ' j) := fun j =>
    ((hκ j).1.comp (infinite F G).continuous).mul (hSc.continuous_indicator continuous_const)
  have hφ's : ∀ j, HasCompactSupport (φ' j) := by
    intro j
    refine HasCompactSupport.intro ((split F G).toHomeomorph.isCompact_preimage.2
      ((hκ j).2.isCompact.prod hVc)) fun g hg => ?_
    change g ∉ split F G ⁻¹' (tsupport (κ j) ×ˢ (V : Set _)) at hg
    simp only [Set.mem_preimage, split_apply, Set.mem_prod, not_and_or] at hg
    rcases hg with hg | hg
    · simp [φ', image_eq_zero_of_notMem_tsupport hg]
    · simp [φ', S, hg]
  let φ : List (InfiniteAdelicGroupPoints.smoothModel F d) → AdelicGroupPoints F G → ℂ :=
    fun a => ∑ j ∈ Finset.univ.filter (fun j => word j = a), φ' j
  refine ⟨Finset.univ.image word, φ, fun a _ => ?_, ?_⟩
  · have hc : Continuous (φ a) := by
      simp only [φ, Finset.sum_fn]
      exact continuous_finsetSum _ fun j _ => hφ'c j
    have hs : HasCompactSupport (φ a) := HasCompactSupport.finset_sum fun j _ => hφ's j
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
    exact ⟨hc.measurable, ⟨C, hC⟩, hs⟩
  · intro E _ _ _ ρ hρ v hv hvL
    set π := ρ.comp (ofInfinite F G).toMonoidHom with hπdef
    have hπ : ∀ w, Continuous fun x => π x w := fun w =>
      hρ.comp ((ofInfinite F G).continuous.prodMk continuous_const)
    have hT : ∀ l, ∀ x w, ρ (ofFinite F G l) (π x w) = π x (ρ (ofFinite F G l) w) := by
      intro l x w
      change ρ (ofFinite F G l) (ρ (ofInfinite F G x) w) = ρ (ofInfinite F G x) (ρ (ofFinite F G l) w)
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
        (factors_commute F G x l).eq]
    have hinv : ∀ j, ∀ l ∈ V, ρ (ofFinite F G l)
        (iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π (word j) v) =
        iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π (word j) v := by
      intro j l hl
      rw [OneParameterParametrix.iteratedLieDerivative_commute π (ρ (ofFinite F G l)) (hT l)
        (word j) hv, hvL l hl.1]
    have hint : ∀ j (u : E), Integrable (fun g => φ' j g • ρ g u)
        (Measure.haar : Measure (AdelicGroupPoints F G)) := fun j u =>
      ((hφ'c j).smul (hρ.comp (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        (hφ's j).smul_right
    calc v = ∑ j, ∫ x, κ j x • π x
          (iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π (word j) v)
          ∂infiniteSliceMeasure (V : Set (FiniteAdelicGroupPoints F G)) := hid E π hπ v hv
      _ = ∑ j, ∫ g, φ' j g • ρ g
          (iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π (word j) v)
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
        Finset.sum_congr rfl fun j _ =>
          (integral_indicator_smul_eq hVo ρ hρ (hκ j).1 _ (hinv j)).symm
      _ = ∑ a ∈ Finset.univ.image word, ∑ j ∈ Finset.univ.filter (fun j => word j = a),
          ∫ g, φ' j g • ρ g
          (iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π (word j) v)
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun j _ => Finset.mem_image_of_mem word (Finset.mem_univ j)) _).symm
      _ = ∑ a ∈ Finset.univ.image word, ∫ g, φ a g • ρ g
          (iteratedLieDerivative 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) π a v)
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [φ, Finset.sum_apply, Finset.sum_smul]
        rw [integral_finsetSum _ fun j _ => hint j _]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [(Finset.mem_filter.1 hj).2]

end Langlands.Global
