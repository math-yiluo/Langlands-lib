import Langlands.Global.AdelicGroupDiscreteSpectrumReduction
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2FiniteApproximationProof
import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2InfiniteAction
import Langlands.Global.AdelicArchimedeanFiniteWeights
import Langlands.Representation.Archimedean.CompactSmoothApproximation
import Mathlib.Analysis.Convex.Integral

/-! # Density of the `K`-finite vectors in closed invariant subspaces of `L²([G])`

For a connected reductive group `G` over a number field `F` and a compact subgroup `K` of
`G(𝔸)`, the vectors of `L²([G])` that are `K_∞`-finite (`K_∞ = K.comap (ofInfinite F G)`) and
fixed by an open subgroup of `G(𝔸_f)` (`IsCanonicalL2FiniteVector`) are dense in every closed
subspace invariant under the right regular representation of `G(𝔸)`
(`subset_closure_canonicalL2FiniteVectors`; Getz–Hahn 2024, Proposition 4.4.7 and Lemma 5.3.7,
as combined in the proof of Lemma 9.7.2). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- A `K`-finite vector of `L²([G])`: its right translates by `K_∞ = K.comap (ofInfinite F G)`
span a finite-dimensional subspace, and it is fixed by an open subgroup of `G(𝔸_f)`. -/
def IsCanonicalL2FiniteVector (hG : IsConnectedReductive G) (K : Subgroup (AdelicGroupPoints F G))
    (w : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K.comap (ofInfinite F G).toMonoidHom =>
      RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter.{0} hG
        (ofInfinite F G (k : InfiniteAdelicGroupPoints F G)) w)) ∧
    ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧
        ∀ l ∈ L, RestrictionSplitCentre.canonicalL2RightAction F G
          centralSplitTorusCharacter.{0} hG (ofFinite F G l) w = w

section Density

variable (hG : IsConnectedReductive G)

local notation "μ" => RestrictionSplitCentre.canonicalMeasure F G
local notation "R" =>
  RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG
local notation "hInvG" =>
  RestrictionSplitCentre.canonicalMeasure_rightInvariant F G centralSplitTorusCharacter hG

/-- The canonical right regular representation on `L²([G])` as bounded operators. -/
def canonicalL2BoundedRightAction :
    AdelicGroupPoints F G →* (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :=
  RestrictionSplitCentre.rationalQuotientL2BoundedRightAction F G μ hInvG

theorem canonicalL2BoundedRightAction_apply (g : AdelicGroupPoints F G) (φ : Lp ℂ 2 μ) :
    canonicalL2BoundedRightAction hG g φ = R g φ := rfl

/-- Orbits of the canonical right regular representation on `L²([G])` are continuous. -/
theorem continuous_canonicalL2RightAction_orbit (φ : Lp ℂ 2 μ) :
    Continuous fun g : AdelicGroupPoints F G => R g φ := by
  have := RestrictionSplitCentre.canonical_finiteIndex F G hG
  have := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  exact (RestrictionSplitCentre.rationalQuotientL2OrbitMap F G hInvG
    (RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup F G)
    (RestrictionSplitCentre.canonical_characterRestrict_injective F G
      centralSplitTorusCharacter hG)
    (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G).1.2
    (RestrictionSplitCentre.isSplitComponent_canonicalComponent F G).1.1.1 φ).continuous

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

/-- **Finite level.** In a closed invariant subspace `V` of `L²([G])`, every vector is a limit of
vectors of `V` fixed by an open subgroup of `G(𝔸_f)`. -/
theorem mem_closure_finiteLevel {V : Submodule ℂ (Lp ℂ 2 μ)}
    (hVc : IsClosed (V : Set (Lp ℂ 2 μ))) (hVinv : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ V, R g x ∈ V)
    {φ : Lp ℂ 2 μ} (hφ : φ ∈ V) :
    φ ∈ closure {w | w ∈ V ∧ ∃ L : Subgroup (FiniteAdelicGroupPoints F G),
      IsOpen (L : Set (FiniteAdelicGroupPoints F G)) ∧ ∀ l ∈ L, R (ofFinite F G l) w = w} := by
  have := RestrictionSplitCentre.canonical_finiteIndex F G hG
  have := AdelicGroupPoints.normOneHaarRightInvariant F G hG.smooth hG.connectedSpace
  have hs := RestrictionSplitCentre.isSplitComponent_canonicalComponent F G
  obtain ⟨Kn, hKn, -, hfix, htend, -⟩ :=
    RestrictionSplitCentre.quotientL2FiniteApproximation F G _ _ _ _
      (RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup F G)
      (RestrictionSplitCentre.canonical_characterRestrict_injective F G
        centralSplitTorusCharacter hG) hs.1.2 hs.1.1.1 hInvG
  refine mem_closure_of_tendsto (htend φ) (Eventually.of_forall fun n => ⟨?_, (Kn n).toSubgroup,
    (Kn n).isOpen, fun l hl => hfix n φ ⟨l, hl⟩⟩)
  let : CompactSpace (Kn n) := isCompact_iff_compactSpace.mp (hKn n)
  rw [RestrictionSplitCentre.rationalQuotientL2FiniteAverage_apply]
  exact (V.restrictScalars ℝ).convex.integral_mem hVc
    (Eventually.of_forall fun k => hVinv _ _ hφ)
    (RestrictionSplitCentre.rationalQuotientL2FiniteAverage_integrable F G
      (RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup F G)
      (RestrictionSplitCentre.canonical_characterRestrict_injective F G
        centralSplitTorusCharacter hG) hs.1.2 hs.1.1.1 hInvG (Kn n) φ)

/-- **Archimedean step.** In a closed invariant subspace `V` of `L²([G])`, a vector fixed by an
open subgroup `L` of `G(𝔸_f)` is a limit of vectors of `V` that are `K_∞`-finite and fixed by
`L`. -/
theorem mem_closure_finiteVector_of_fixed {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {V : Submodule ℂ (Lp ℂ 2 μ)}
    (hVc : IsClosed (V : Set (Lp ℂ 2 μ))) (hVinv : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ V, R g x ∈ V)
    {w : Lp ℂ 2 μ} (hwV : w ∈ V) {L : Subgroup (FiniteAdelicGroupPoints F G)}
    (hL : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    (hLw : ∀ l ∈ L, R (ofFinite F G l) w = w) :
    w ∈ closure {w' | w' ∈ V ∧ IsCanonicalL2FiniteVector hG K w'} := by
  classical
  have := hG.isAffineHom
  -- The archimedean part of `K`, as a compact subgroup of `G(𝔸)`.
  set C : Subgroup (AdelicGroupPoints F G) := K ⊓ (finite F G).toMonoidHom.ker with hCdef
  have hC1 : ∀ c ∈ C, finite F G c = 1 := fun c hc => hc.2
  have hCc : IsCompact (C : Set (AdelicGroupPoints F G)) :=
    hKc.inter_right (isClosed_singleton.preimage (finite F G).continuous)
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  let : MeasurableSpace C := borel C
  have : BorelSpace C := ⟨rfl⟩
  set ν : Measure C := Langlands.Analysis.compactProbabilityHaar C with hν
  -- Elements of `C` are archimedean, so they commute with `G(𝔸_f)`.
  have hCcomm : ∀ (c : C) (l : FiniteAdelicGroupPoints F G),
      (c : AdelicGroupPoints F G) * ofFinite F G l = ofFinite F G l * c := by
    intro c l
    have hc : ofInfinite F G (infinite F G (c : AdelicGroupPoints F G)) = c := by
      rw [ofInfinite_eq_pair, ← hC1 c c.2, pair_projections]
    rw [← hc]
    exact (AdelicGroupPoints.factors_commute F G _ l).eq
  -- The orbit of `w` under `C`.
  let Fo : C(C, Lp ℂ 2 μ) := ⟨fun c => R (c : AdelicGroupPoints F G) w,
    (continuous_canonicalL2RightAction_orbit hG w).comp continuous_subtype_val⟩
  have hFo : ∀ c : C, Fo c = R (c : AdelicGroupPoints F G) w := fun c => rfl
  have hint : ∀ a : C(C, ℂ), Integrable (fun c => a c • Fo c) ν := fun a =>
    (a.continuous.smul Fo.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  -- The averaging map `a ↦ ∫ a(c) R(c) w dc`.
  let T : C(C, ℂ) →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun a => ∫ c, a c • Fo c ∂ν
      map_add' := fun a b => by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun z a => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul z _ }
  have hT : ∀ a, T a = ∫ c, a c • Fo c ∂ν := fun a => rfl
  -- The averages lie in `V`.
  have hTV : ∀ a, T a ∈ V := fun a =>
    (V.restrictScalars ℝ).convex.integral_mem hVc
      (Eventually.of_forall fun c => V.smul_mem _ (hVinv _ _ hwV)) (hint a)
  -- Translation by `C` intertwines `T` with the left regular action.
  have hTtrans : ∀ (h : C) (a : C(C, ℂ)),
      R (h : AdelicGroupPoints F G) (T a) =
        T (Langlands.CompactRepresentativeWeights.leftRegular h a) := by
    intro h a
    rw [hT, hT, ← canonicalL2BoundedRightAction_apply hG,
      ← (canonicalL2BoundedRightAction hG (h : AdelicGroupPoints F G)).integral_comp_comm
        (hint a),
      ← integral_mul_left_eq_self
        (fun c => (Langlands.CompactRepresentativeWeights.leftRegular h a) c • Fo c) h]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    simp only [map_smul, canonicalL2BoundedRightAction_apply, hFo,
      Langlands.CompactRepresentativeWeights.leftRegular_apply, inv_mul_cancel_left,
      Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  -- Translation by an open level fixing `w` fixes the averages.
  have hTlevel : ∀ a, ∀ l ∈ L, R (ofFinite F G l) (T a) = T a := by
    intro a l hl
    rw [hT, ← canonicalL2BoundedRightAction_apply hG,
      ← (canonicalL2BoundedRightAction hG (ofFinite F G l)).integral_comp_comm (hint a)]
    refine integral_congr_ae (Eventually.of_forall fun c => ?_)
    simp only [map_smul, canonicalL2BoundedRightAction_apply, hFo]
    rw [← Module.End.mul_apply, ← map_mul, ← hCcomm c l, map_mul, Module.End.mul_apply,
      hLw l hl]
  -- Averages of weights with finite left-translation orbit are `K`-finite.
  have hTfin : ∀ b ∈ (Langlands.CompactRepresentativeWeights.finiteWeights (K := C) :
      Set C(C, ℂ)), IsCanonicalL2FiniteVector hG K (T b) := by
    intro b hb
    let ρC : Representation ℂ C (Lp ℂ 2 μ) := MonoidHom.comp (R) C.subtype
    let Tint : (Langlands.CompactRepresentativeWeights.leftRegular (K := C)).IntertwiningMap ρC :=
      { toLinearMap := T
        isIntertwining' := fun h => LinearMap.ext fun a => (hTtrans h a).symm }
    have hfin : FiniteVectors.IsFiniteVector ρC (T b) :=
      (show FiniteVectors.IsFiniteVector
        (Langlands.CompactRepresentativeWeights.leftRegular (K := C)) b from hb).map Tint
    refine ⟨?_, L, hL, fun l hl => hTlevel b l hl⟩
    have : Module.Finite ℂ (FiniteVectors.orbitSpan ρC (T b)) := hfin
    apply Submodule.finiteDimensional_of_le (S₂ := FiniteVectors.orbitSpan ρC (T b))
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    have hk : ofInfinite F G (k : InfiniteAdelicGroupPoints F G) ∈ C :=
      ⟨k.2, finite_ofInfinite F G _⟩
    exact FiniteVectors.action_mem_orbitSpan ρC ⟨_, hk⟩ (T b)
  -- Approximation.
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hU : {c : C | ‖Fo c - w‖ < ε / 2} ∈ 𝓝 (1 : C) := by
    refine IsOpen.mem_nhds (isOpen_lt (Fo.continuous.sub continuous_const).norm continuous_const) ?_
    change ‖R ((1 : C) : AdelicGroupPoints F G) w - w‖ < ε / 2
    rw [Subgroup.coe_one, map_one, Module.End.one_apply, sub_self, norm_zero]
    exact half_pos hε
  obtain ⟨a, haU, ha1, hanorm⟩ :=
    Langlands.Archimedean.CompactSmoothAverage.exists_normalized_weight ν (1 : C) hU
  have h1 : ‖T a - w‖ ≤ ε / 2 :=
    Langlands.Archimedean.CompactSmoothAverage.norm_integral_average_sub_le_of_support ν a Fo w
      ha1 hanorm (fun c hc => (haU c hc).le)
  have hdense := AdelicGroupPoints.dense_archimedean_finiteWeights F G C hC1
  set δ : ℝ := ε / (2 * (‖w‖ + 1)) with hδ
  have hδpos : 0 < δ := div_pos hε (by positivity)
  obtain ⟨b, hb, hab⟩ := Metric.mem_closure_iff.mp
    (by rw [hdense.closure_eq]; exact Set.mem_univ a) δ hδpos
  have h2 : ‖T a - T b‖ ≤ δ * ‖w‖ := by
    rw [← map_sub, hT]
    have hbound : ∀ᵐ c ∂ν, ‖(a - b) c • Fo c‖ ≤ δ * ‖w‖ := Eventually.of_forall fun c => by
      rw [norm_smul, hFo, norm_canonicalL2RightAction hG]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg w)
      exact ((a - b).norm_coe_le_norm c).trans (by rw [← dist_eq_norm]; exact hab.le)
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound
  refine ⟨T b, ⟨hTV b, hTfin b hb⟩, ?_⟩
  have h3 : δ * ‖w‖ < ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [norm_nonneg w]
  calc dist w (T b) = ‖(w - T a) + (T a - T b)‖ := by rw [dist_eq_norm]; abel_nf
    _ ≤ ‖w - T a‖ + ‖T a - T b‖ := norm_add_le _ _
    _ < ε := by rw [norm_sub_rev] at h1; linarith

/-- **Density of the `K`-finite vectors** (Getz–Hahn 2024, Proposition 4.4.7 and Lemma 5.3.7, as
combined in the proof of Lemma 9.7.2). For a compact subgroup `K` of `G(𝔸)`, every vector of a
closed subspace `V` of `L²([G])` invariant under the right regular representation is a limit of
vectors of `V` that are `K_∞`-finite and fixed by an open subgroup of `G(𝔸_f)`. -/
theorem subset_closure_canonicalL2FiniteVectors {K : Subgroup (AdelicGroupPoints F G)}
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {V : Submodule ℂ (Lp ℂ 2 μ)}
    (hVc : IsClosed (V : Set (Lp ℂ 2 μ)))
    (hVinv : ∀ (g : AdelicGroupPoints F G), ∀ x ∈ V, R g x ∈ V) :
    (V : Set (Lp ℂ 2 μ)) ⊆ closure {w | w ∈ V ∧ IsCanonicalL2FiniteVector hG K w} := by
  intro φ hφ
  refine closure_minimal ?_ isClosed_closure (mem_closure_finiteLevel hG hVc hVinv hφ)
  rintro w ⟨hwV, L, hL, hLw⟩
  exact mem_closure_finiteVector_of_fixed hG hKc hVc hVinv hwV hL hLw

end Density

end Langlands.Global
