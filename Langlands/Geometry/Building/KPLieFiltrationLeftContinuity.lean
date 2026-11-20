import Langlands.Geometry.Building.KPLieGradedAction
import Langlands.Geometry.Building.ActualAffineRootLocalFiniteness

/-!
# Left continuity of the Moy–Prasad Lie filtration on supplied data

The predicate `IsLeftContinuousAt` of `KPLieGradedAction` is reduced to conditions on the supplied
data: left continuity of the supplied centralizer lattices `z_r`, and the absence of affine-root
values at `x` in a short interval below each depth. The latter follows from the Library's
bounded finiteness of the actual affine roots under `RelativeRoot.HasOppositeFactorPairs`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {L : P.LieFiltrationData}

/-! ### Cancelling a uniformizer -/

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In the `F`-vector space `𝔤`, if `ϖ • Z ∈ 𝔪 • M` for a uniformizer `ϖ`, then `Z ∈ M`. -/
theorem mem_of_smul_mem_maximalIdeal_smul [IsDiscreteValuationRing 𝒪[F]]
    {M : Submodule 𝒪[F] (GenericLie 𝒪[F] G)} {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {Z : GenericLie 𝒪[F] G} (h : ϖ • Z ∈ 𝓂[F] • M) : Z ∈ M := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    Submodule.ideal_span_singleton_smul] at h
  obtain ⟨Y, hY, e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
  have hϖ0 : (algebraMap 𝒪[F] F ϖ) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective 𝒪[F] F)]
    exact hϖ.ne_zero
  have e' : (algebraMap 𝒪[F] F ϖ) • Y = (algebraMap 𝒪[F] F ϖ) • Z := by
    rw [algebraMap_smul, algebraMap_smul, e]
  rwa [← smul_right_injective _ hϖ0 e']

/-! ### From the non-negative indices to all real indices -/

/-- Left continuity of the real-depth filtration at every real `t` follows, under periodicity, from
left continuity of the supplied lattices `𝔤_{x,τ}` at every `τ > 0`. -/
theorem isLeftContinuousAt_of_lieFiltration (hL : L.IsPeriodic) {x : P.Apartment}
    (hN : ∀ τ : NNReal, 0 < τ → ∃ s < (τ : ℝ),
      ∀ u : NNReal, s < u → u ≤ τ → L.lieFiltration x u ≤ L.lieFiltration x τ)
    (t : ℝ) : L.IsLeftContinuousAt x t := by
  set n := indexShift t with hn
  have hτ : (shiftedIndex t : ℝ) = t + n := rfl
  rcases lt_or_eq_of_le (show (0 : NNReal) ≤ shiftedIndex t from bot_le) with hpos | hzero
  · -- `t + n > 0`: near `t` the shift is still `n`.
    obtain ⟨s', hs', h'⟩ := hN _ hpos
    have hpos' : (0 : ℝ) < t + n := by rw [← hτ]; exact_mod_cast hpos
    refine ⟨max (s' - n) (-n), max_lt (by rw [hτ] at hs'; linarith) (by linarith), ?_⟩
    intro u hsu hut X hX
    have hu1 : s' - n < u := (le_max_left _ _).trans_lt hsu
    have hu2 : -(n : ℝ) < u := (le_max_right _ _).trans_lt hsu
    have hnu : indexShift u = n := by
      apply le_antisymm
      · exact Nat.ceil_le.2 (by linarith)
      · exact Nat.ceil_mono (neg_le_neg hut)
    have hsu' : (shiftedIndex u : ℝ) = u + n := by
      change u + (indexShift u : ℝ) = u + n
      rw [hnu]
    rw [mem_lieFiltrationReal] at hX ⊢
    intro a ha
    rw [← hn, ← hnu] at ha
    refine h' (shiftedIndex u) (by rw [hsu']; linarith) ?_ (hX a ha)
    rw [← NNReal.coe_le_coe, hsu', hτ]
    linarith
  · -- `t = -n`: just below `t` the shift is `n + 1`; use continuity at `1` and periodicity.
    have ht : t + n = 0 := by rw [← hτ, ← hzero]; rfl
    obtain ⟨s', hs', h'⟩ := hN 1 one_pos
    refine ⟨max (s' - (n + 1)) (t - 1), max_lt (by push_cast at hs'; linarith) (by linarith), ?_⟩
    intro u hsu hut
    rcases hut.lt_or_eq with hlt | rfl
    swap
    · exact le_rfl
    intro X hX
    have hu1 : s' - (n + 1) < u := (le_max_left _ _).trans_lt hsu
    have hu2 : t - 1 < u := (le_max_right _ _).trans_lt hsu
    have hnu : indexShift u = n + 1 := by
      apply le_antisymm
      · exact Nat.ceil_le.2 (by push_cast; linarith)
      · exact Nat.add_one_le_iff.2 (Nat.lt_ceil.2 (by linarith))
    have hsu' : (shiftedIndex u : ℝ) = u + (n + 1) := by
      change u + (indexShift u : ℝ) = u + (n + 1)
      rw [hnu]
      push_cast
      ring
    rw [mem_lieFiltrationReal] at hX ⊢
    intro b hb
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    have hϖm : ϖ ∈ 𝓂[F] := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
      exact Ideal.mem_span_singleton_self ϖ
    have hmem : (ϖ * b) • X ∈ L.lieFiltration x 1 := by
      refine h' (shiftedIndex u) (by rw [hsu']; linarith) ?_ (hX _ ?_)
      · rw [← NNReal.coe_le_coe, hsu']
        push_cast
        linarith
      · rw [hnu, pow_succ, mul_comm ϖ b]
        exact Ideal.mul_mem_mul hb hϖm
    have h1 : L.lieFiltration x 1 = 𝓂[F] • L.lieFiltration x 0 := by
      rw [← hL x 0, zero_add]
    rw [h1, mul_smul] at hmem
    have h0 : shiftedIndex t = 0 := hzero.symm
    rw [h0]
    exact mem_of_smul_mem_maximalIdeal_smul hϖ hmem

/-! ### Left continuity of the supplied lattices -/

/-- If `z_u ⊆ z_τ` and every affine root `ψ` with `ψ(x) ≥ u` also has `ψ(x) ≥ τ`, then
`𝔤_{x,u} ⊆ 𝔤_{x,τ}`. -/
theorem lieFiltration_le_of_forall (x : P.Apartment) {u τ : NNReal}
    (hz : L.centralizerLie u ≤ L.centralizerLie τ)
    (hψ : ∀ ψ : P.affineRoots, (u : ℝ) ≤ ψ.1 x → (τ : ℝ) ≤ ψ.1 x) :
    L.lieFiltration x u ≤ L.lieFiltration x τ :=
  sup_le ((Submodule.map_mono hz).trans le_sup_left)
    (iSup₂_le fun ψ hψu => le_sup_of_le_right (le_iSup₂_of_le ψ (hψ ψ hψu) le_rfl))

/-- Under `HasOppositeFactorPairs`, below every real `τ` there is an interval `(s, τ)` containing
no value `ψ(x)` of an affine root. -/
theorem exists_lt_forall_affineRoots_of_oppositePairs
    (hF : RelativeRoot.HasOppositeFactorPairs P.i) (x : P.Apartment) (τ : ℝ) :
    ∃ s < τ, ∀ ψ ∈ P.affineRoots, s < ψ x → τ ≤ ψ x := by
  have hT := P.finite_bounded_affineRoots_of_oppositePairs hF x (fun _ => |τ| + 1)
  set W : Set ℝ := (fun ψ => ψ x) '' {ψ | ψ ∈ P.affineRoots ∧ |ψ x| ≤ |τ| + 1 ∧ ψ x < τ}
  have hW : W.Finite := (hT.subset fun ψ hψ => ⟨hψ.1, hψ.2.1⟩).image _
  set S : Finset ℝ := insert (τ - 1) hW.toFinset
  have hS : S.Nonempty := ⟨_, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hS, (Finset.max'_lt_iff _ _).2 fun v hv => ?_, fun ψ hψ hsψ => ?_⟩
  · rcases Finset.mem_insert.1 hv with rfl | hv
    · linarith
    · obtain ⟨ψ, hψ, rfl⟩ := hW.mem_toFinset.1 hv
      exact hψ.2.2
  · by_contra hlt
    replace hlt := not_le.1 hlt
    have h1 : τ - 1 < ψ x :=
      (Finset.le_max' _ _ (Finset.mem_insert_self _ _)).trans_lt hsψ
    have hmem : ψ x ∈ W := ⟨ψ, ⟨hψ, abs_le.2 ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩,
      hlt⟩, rfl⟩
    have h2 : ψ x ≤ S.max' hS :=
      Finset.le_max' _ _ (Finset.mem_insert_of_mem (hW.mem_toFinset.2 hmem))
    linarith

/-- Under `HasOppositeFactorPairs`, left continuity of the supplied centralizer lattices `z_r` at
`τ` gives left continuity of `𝔤_{x,r}`, `r ≥ 0`, at `τ`. -/
theorem exists_lieFiltration_le_of_oppositePairs (hF : RelativeRoot.HasOppositeFactorPairs P.i)
    (x : P.Apartment) (τ : NNReal)
    (hz : ∃ s < (τ : ℝ), ∀ u : NNReal, s < u → u ≤ τ → L.centralizerLie u ≤ L.centralizerLie τ) :
    ∃ s < (τ : ℝ), ∀ u : NNReal, s < u → u ≤ τ → L.lieFiltration x u ≤ L.lieFiltration x τ := by
  obtain ⟨s₁, hs₁, h₁⟩ := hz
  obtain ⟨s₂, hs₂, h₂⟩ := exists_lt_forall_affineRoots_of_oppositePairs hF x τ
  refine ⟨max s₁ s₂, max_lt hs₁ hs₂, fun u hsu hut => ?_⟩
  refine lieFiltration_le_of_forall x (h₁ u ((le_max_left _ _).trans_lt hsu) hut) ?_
  intro ψ hψ
  exact h₂ ψ.1 ψ.2 (((le_max_right _ _).trans_lt hsu).trans_le hψ)

variable (L) in
/-- The supplied centralizer lattices `z_r` are left-continuous at every `τ > 0`: there is `s < τ`
with `z_u ⊆ z_τ` (hence `z_u = z_τ`, the family being decreasing) for `s < u ≤ τ`. -/
def IsCentralizerLieLeftContinuous : Prop :=
  ∀ τ : NNReal, 0 < τ → ∃ s < (τ : ℝ),
    ∀ u : NNReal, s < u → u ≤ τ → L.centralizerLie u ≤ L.centralizerLie τ

/-- Under periodicity and `HasOppositeFactorPairs`, if the supplied centralizer lattices `z_r` are
left-continuous at every `τ > 0`, then the real-depth filtration is left-continuous at every real
`t`. -/
theorem isLeftContinuousAt_of_oppositePairs (hL : L.IsPeriodic)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i)
    (hz : L.IsCentralizerLieLeftContinuous)
    (x : P.Apartment) (t : ℝ) : L.IsLeftContinuousAt x t :=
  isLeftContinuousAt_of_lieFiltration hL
    (fun τ hτ => exists_lieFiltration_le_of_oppositePairs hF x τ (hz τ hτ)) t

/-- Under the same hypotheses, a subgroup acting trivially on `𝔤_{x,-r}/𝔤_{x,(-r)+}` acts trivially
on `𝔤*_{x,r}/𝔤*_{x,r+}`. -/
theorem actsTriviallyOnDualGraded_of_oppositePairs (hL : L.IsPeriodic)
    (hF : RelativeRoot.HasOppositeFactorPairs P.i)
    (hz : L.IsCentralizerLieLeftContinuous)
    {x : P.Apartment} {r : ℝ} {N : Subgroup (rationalPoints G)}
    (hN : L.ActsTriviallyOnGraded x (-r) N) : L.ActsTriviallyOnDualGraded x r N :=
  actsTriviallyOnDualGraded_of_isLeftContinuousAt hL
    (isLeftContinuousAt_of_oppositePairs hL hF hz x (-r)) hN

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
