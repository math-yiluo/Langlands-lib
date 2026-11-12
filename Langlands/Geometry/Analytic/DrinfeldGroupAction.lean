import Langlands.Geometry.Analytic.DrinfeldAction
import Langlands.Geometry.Analytic.DirectedAtlasMaps
import Langlands.Geometry.Analytic.CompatibleStrongSaturationFunctor
import Langlands.Geometry.Analytic.ContinuousAnalyticAction

/-! # The action of `GL_{d+1}(F)` on Drinfeld's upper half space -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra GeneralizedTateAlgebra CategoryTheory

/-! ## Strong maps into atlases with totally ordered charts -/

namespace IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X]

/-- Any two chart images are comparable for inclusion. -/
def HasChainCharts (a : IndexedAffinoidAtlas.{u, v, w} K X) : Prop :=
  ∀ i j : a.Index, Set.range (a.chart i) ⊆ Set.range (a.chart j) ∨
    Set.range (a.chart j) ⊆ Set.range (a.chart i)

theorem HasChainCharts.hasDirectedCharts {a : IndexedAffinoidAtlas.{u, v, w} K X}
    (h : a.HasChainCharts) : a.HasDirectedCharts := fun i j =>
  (h i j).elim (fun hij => ⟨j, hij, Subset.rfl⟩) (fun hji => ⟨i, Subset.rfl, hji⟩)

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Every strong map into an atlas with totally ordered charts has coherent pullbacks: of two
admissible target charts one contains the other, and the two pullbacks differ by the
restriction between them. -/
theorem hasCoherentPullbacks_of_chain (f : StrongHom A B) (hb : B.atlas.HasChainCharts) :
    f.HasCoherentPullbacks := by
  intro i j k hj hk T η m hmj hmk α hα
  rcases hb j k with hjk | hkj
  · have e : f.pullback i k hk = (f.pullback i j hj).comp (B.atlas.restriction j k hjk) := by
      have h := f.restriction_comm i i j k Subset.rfl hjk hj hk
      rwa [A.atlas.restriction_id, BoundedAlgHom.id_comp] at h
    rw [e, ← BoundedAlgHom.comp_assoc, ← hα, BoundedAlgHom.comp_assoc,
      ← B.atlas.restriction_comp]
  · have e : f.pullback i j hj = (f.pullback i k hk).comp (B.atlas.restriction k j hkj) := by
      have h := f.restriction_comm i i k j Subset.rfl hkj hk hj
      rwa [A.atlas.restriction_id, BoundedAlgHom.id_comp] at h
    apply B.atlas.restriction_hom_ext k j hkj T
    rw [BoundedAlgHom.comp_assoc, ← e, ← hα, BoundedAlgHom.comp_assoc,
      ← B.atlas.restriction_comp]

end StrongHom

namespace CompatibleStrongHom

/-- The compatible strong map of a chosen-target map into an atlas with totally ordered
charts: the existing directed construction `StrongHom.ofDirected`. -/
def ofChain (f : A ⟶ B) (hb : B.atlas.HasChainCharts) : CompatibleStrongHom A B where
  toStrongHom := StrongHom.ofDirected f hb.hasDirectedCharts
  compatible := (StrongHom.ofDirected f hb.hasDirectedCharts).hasLocallyCompatiblePullbacks_iff.mpr
    ((StrongHom.ofDirected f hb.hasDirectedCharts).hasCoherentPullbacks_of_chain hb)

@[simp]
theorem ofChain_baseMap (f : A ⟶ B) (hb : B.atlas.HasChainCharts) :
    (ofChain f hb).baseMap = f.baseMap := rfl

theorem ofChain_pullback_selected (f : A ⟶ B) (hb : B.atlas.HasChainCharts)
    (i : A.atlas.Index) :
    (ofChain f hb).pullback i (f.indexMap i) (f.image_chart_subset i) = f.pullback i :=
  StrongHom.ofDirected_pullback_selected f hb.hasDirectedCharts i

/-- At a target chart containing the selected one, the pullback is the selected pullback
followed by restriction. -/
theorem ofChain_pullback_upper (f : A ⟶ B) (hb : B.atlas.HasChainCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hs : Set.range (B.atlas.chart (f.indexMap i)) ⊆ Set.range (B.atlas.chart j)) :
    (ofChain f hb).pullback i j h =
      (f.pullback i).comp (B.atlas.restriction (f.indexMap i) j hs) := by
  have e := f.directedPullback_comp_restriction hb.hasDirectedCharts i j h j hs Subset.rfl
  rw [B.atlas.restriction_id, BoundedAlgHom.comp_id] at e
  exact e

end CompatibleStrongHom

end AffinoidAtlasPresentation

/-! ## Linear forms under maps with prescribed coordinates -/

namespace DrinfeldUpperHalfSpace

open AnalyticAffineSpace ExhaustionIndex

variable {F : Type v} [NontriviallyNormedField F] [ProperSpace F]
  (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra F K] {d : ℕ}

section

variable (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)

/-- A map out of a polydisc algebra sending each `Tᵢ` to `ℓ_{g_{i+1}} / ℓ_{g_0}` sends `ℓ_a` to
`ℓ_{a g} / ℓ_{g_0}`. -/
theorem map_linearForm_of_coordinate (N m : ℕ)
    (χ : BoundedAlgHom K (disc K d m) (exhaustionChart F K d N).algebra)
    (hχ : ∀ i, χ (coordinate K (disc K d m) i) = actionTuple K g hg N i)
    (a : Fin (d + 1) → F) :
    χ (linearForm K d m (coefficients F K d a)) =
      (exhaustionChart F K d N).baseMap
        (linearForm K d N (coefficients F K d (Matrix.vecMul a g))) * inverse F K d hg N := by
  have hlhs : χ (linearForm K d m (coefficients F K d a)) =
      algebraMap K (exhaustionChart F K d N).algebra (algebraMap F K (a 0)) +
        ∑ i : Fin d, algebraMap K (exhaustionChart F K d N).algebra (algebraMap F K (a i.succ)) *
          actionTuple K g hg N i := by
    change χ.toAlgHom (algebraMap K (disc K d m) (algebraMap F K (a 0)) +
      ∑ i : Fin d, algebraMap F K (a i.succ) • coordinate K (disc K d m) i) = _
    rw [map_add, AlgHom.commutes, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    congr 1
    exact hχ i
  have hrhs : (exhaustionChart F K d N).baseMap
        (linearForm K d N (coefficients F K d (Matrix.vecMul a g))) * inverse F K d hg N =
      ∑ k, algebraMap K (exhaustionChart F K d N).algebra (algebraMap F K (a k)) *
        ((exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d (g k))) *
          inverse F K d hg N) := by
    rw [linearForm_vecMul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, mul_assoc]
  rw [hlhs, hrhs, Fin.sum_univ_succ]
  have h0 : (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d (g 0))) *
      inverse F K d hg N = 1 :=
    linearForm_mul_inverse F K d hg N
  rw [h0, mul_one]
  rfl

end

variable (F d) in
/-- An inverse of `ℓ_c` in the chart algebra of `V_N` is the constructed one. -/
theorem eq_inverse_of_mul_eq_one {c : Fin (d + 1) → F} (hc : c ≠ 0) (N : ℕ)
    {w : (exhaustionChart F K d N).algebra}
    (hw : (exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c)) * w = 1) :
    w = inverse F K d hc N := by
  calc w = ((exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c)) *
        inverse F K d hc N) * w := by rw [linearForm_mul_inverse, one_mul]
    _ = inverse F K d hc N *
        ((exhaustionChart F K d N).baseMap (linearForm K d N (coefficients F K d c)) * w) := by
      ring
    _ = inverse F K d hc N := by rw [hw, mul_one]

/-! ## Pullbacks with prescribed coordinates -/

variable [NeZero d]

/-- A bounded map from the chart algebra of the member `T` to that of `U` sending each
coordinate `Tᵢ` to `ℓ_{g_{i+1}} / ℓ_{g_0}`: the algebraic form of the pullback along
`z ↦ g · z` from `T` to `U`. -/
def IsActionPullback (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)
    (U T : ExhaustionIndex F K d)
    (φ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra) : Prop :=
  ∀ i : Fin d, φ ((exhaustionChart F K d T.level).baseMap
    (coordinate K (disc K d T.level) i)) = actionTuple K g hg U.level i

section

variable {K} {g : Fin (d + 1) → Fin (d + 1) → F} {hg : g 0 ≠ 0} {U T : ExhaustionIndex F K d}

omit [NeZero d] in
/-- There is at most one such pullback. -/
theorem IsActionPullback.eq
    {φ ψ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra}
    (hφ : IsActionPullback K g hg U T φ) (hψ : IsActionPullback K g hg U T ψ) : φ = ψ := by
  apply (RationalChart.represents (exhaustionChart F K d T.level)).hom_ext
  apply hom_ext_coordinate
  intro i
  exact (hφ i).trans (hψ i).symm

/-- Restriction to a larger target member. -/
theorem IsActionPullback.comp_res {T' : ExhaustionIndex F K d} (h : T.1 ⊆ T'.1)
    {φ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra}
    (hφ : IsActionPullback K g hg U T φ) :
    IsActionPullback K g hg U T' (φ.comp (exhaustionRes K h)) := fun i =>
  (congrArg φ (exhaustionRes_coordinate K h i)).trans (hφ i)

omit [NeZero d] in
/-- Composition: the pullback along `g'` followed by the pullback along `g` is the pullback
along the matrix product `g g'`, whose rows are `g_k g'`. -/
theorem IsActionPullback.comp {g' : Fin (d + 1) → Fin (d + 1) → F} {hg' : g' 0 ≠ 0}
    {T₂ : ExhaustionIndex F K d}
    {φ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra}
    {ψ : BoundedAlgHom K (exhaustionChart F K d T₂.level).algebra
      (exhaustionChart F K d T.level).algebra}
    (hφ : IsActionPullback K g' hg' U T φ) (hψ : IsActionPullback K g hg T T₂ ψ)
    {g'' : Fin (d + 1) → Fin (d + 1) → F} (hg'' : g'' 0 ≠ 0)
    (e : g'' = fun k => Matrix.vecMul (g k) g') :
    IsActionPullback K g'' hg'' U T₂ (φ.comp ψ) := by
  subst e
  intro i
  set β := (exhaustionChart F K d U.level).baseMap
  set u' := inverse F K d hg' U.level
  have hχ := map_linearForm_of_coordinate K g' hg' U.level T.level
    (φ.comp (exhaustionChart F K d T.level).baseMap) hφ
  have hw : β (linearForm K d U.level (coefficients F K d (Matrix.vecMul (g 0) g'))) *
      (u' * φ (inverse F K d hg T.level)) = 1 := by
    have h1 := congrArg φ (linearForm_mul_inverse F K d hg T.level)
    rw [map_mul, map_one] at h1
    change φ ((exhaustionChart F K d T.level).baseMap
      (linearForm K d T.level (coefficients F K d (g 0)))) * _ = 1 at h1
    rw [show φ ((exhaustionChart F K d T.level).baseMap
      (linearForm K d T.level (coefficients F K d (g 0)))) = _ from hχ (g 0)] at h1
    rw [← mul_assoc]
    exact h1
  have hinv := eq_inverse_of_mul_eq_one F K d hg'' U.level hw
  change φ (ψ ((exhaustionChart F K d T₂.level).baseMap
    (coordinate K (disc K d T₂.level) i))) = _
  rw [hψ i]
  unfold actionTuple
  rw [map_mul]
  rw [show φ ((exhaustionChart F K d T.level).baseMap
    (linearForm K d T.level (coefficients F K d (g i.succ)))) = _ from hχ (g i.succ),
    mul_assoc, hinv]

end

/-! ## The identity matrix -/

omit [IsUltrametricDist K] [CompleteSpace K] [ProperSpace F] [NeZero d] in
theorem coefficients_entries_one (k : Fin (d + 1)) :
    coefficients F K d (entries (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) k) =
      Pi.single k 1 := by
  ext j
  by_cases h : k = j
  · subst h
    simp [coefficients, entries]
  · simp [coefficients, entries, h, Ne.symm h]

omit [CompleteSpace K] [ProperSpace F] [NeZero d] in
theorem linearForm_single_zero (m : ℕ) :
    linearForm K d m (Pi.single 0 1) = 1 := by
  simp [linearForm, Fin.succ_ne_zero]

omit [CompleteSpace K] [ProperSpace F] [NeZero d] in
theorem linearForm_single_succ (m : ℕ) (i : Fin d) :
    linearForm K d m (Pi.single i.succ 1) = coordinate K (disc K d m) i := by
  unfold linearForm
  rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, map_zero, zero_add,
    Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_smul]
  · intro j _ hj
    rw [Pi.single_eq_of_ne (fun h => hj (Fin.succ_injective _ h)), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [NeZero d] in
theorem inverse_one (N : ℕ) :
    inverse F K d (entries_row_zero_ne_zero (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F)) N =
      1 := by
  refine (eq_inverse_of_mul_eq_one F K d _ N ?_).symm
  rw [coefficients_entries_one, linearForm_single_zero, map_one, one_mul]

omit [NeZero d] in
theorem actionTuple_one (N : ℕ) (i : Fin d) :
    actionTuple K (entries (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F))
        (entries_row_zero_ne_zero 1) N i =
      (exhaustionChart F K d N).baseMap (coordinate K (disc K d N) i) := by
  unfold actionTuple
  rw [inverse_one, mul_one, coefficients_entries_one, linearForm_single_succ]

omit [NeZero d] in
/-- The identity is the pullback along the identity matrix. -/
theorem isActionPullback_id (U : ExhaustionIndex F K d) :
    IsActionPullback K (entries (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F))
      (entries_row_zero_ne_zero 1) U U
      (BoundedAlgHom.id K (exhaustionChart F K d U.level).algebra) := fun i =>
  (actionTuple_one K U.level i).symm

/-! ## Points -/

section

variable (g : Fin (d + 1) → Fin (d + 1) → F) (hg : g 0 ≠ 0)

omit [NeZero d] in
/-- A map out of a polydisc algebra with the coordinates of `g` computes `g · x`. -/
theorem chart_eq_chartAction (U : ExhaustionIndex F K d) (m : ℕ)
    (χ : BoundedAlgHom K (disc K d m) (exhaustionChart F K d U.level).algebra)
    (hχ : ∀ i, χ (coordinate K (disc K d m) i) = actionTuple K g hg U.level i)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    chart K d m (BanachSpectrum.comap χ.toBoundedRingHom x) = chartAction K g hg U x := by
  unfold chartAction actionPoint
  have hm := le_max_left m (actionLevel K g hg U.level)
  have hn := le_max_right m (actionLevel K g hg U.level)
  have hmaps : χ.comp (restriction K d hm) =
      (actionHom K g hg U.level _ (actionLevel_spec K g hg U.level)).comp
        (restriction K d hn) := by
    apply hom_ext_coordinate
    intro i
    change χ (restriction K d hm (coordinate K (disc K d _) i)) =
      actionHom K g hg U.level _ (actionLevel_spec K g hg U.level)
        (restriction K d hn (coordinate K (disc K d _) i))
    exact (congrArg χ (disc_restriction_coordinate K d hm i)).trans ((hχ i).trans
      ((actionHom_coordinate K g hg _ _ (actionLevel_spec K g hg U.level) i).symm.trans
        (congrArg _ (disc_restriction_coordinate K d hn i).symm)))
  rw [← chart_pull K d hm, ← chart_pull K d hn]
  congr 1
  apply BanachSpectrum.ext
  intro f
  exact congrArg (fun φ : BoundedAlgHom K (disc K d (max m (actionLevel K g hg U.level)))
    (exhaustionChart F K d U.level).algebra => x (φ f)) hmaps

end

section

variable {g : Fin (d + 1) → Fin (d + 1) → F} {hg : g 0 ≠ 0}

theorem IsActionPullback.chart_eq {U T : ExhaustionIndex F K d}
    {φ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra}
    (hφ : IsActionPullback K g hg U T φ)
    (x : BanachSpectrum (exhaustionChart F K d U.level).algebra) :
    (exhaustionChartMap F K d T (BanachSpectrum.comap φ.toBoundedRingHom x)).1 =
      chartAction K g hg U x :=
  chart_eq_chartAction K g hg U T.level (φ.comp (exhaustionChart F K d T.level).baseMap) hφ x

end

theorem mem_exhaustionChartMap (T : ExhaustionIndex F K d)
    (y : BanachSpectrum (exhaustionChart F K d T.level).algebra) :
    (exhaustionChartMap F K d T y).1 ∈ T.1 := by
  have h := mem_range_self (f := exhaustionChartMap F K d T) y
  rw [range_exhaustionChartMap] at h
  exact h

theorem exists_exhaustionChartMap_eq (z : Omega F K d) :
    ∃ (U : ExhaustionIndex F K d) (x : BanachSpectrum (exhaustionChart F K d U.level).algebra),
      exhaustionChartMap F K d U x = z := by
  obtain ⟨N, hN⟩ := exists_mem_exhaustion F K d z.2
  have hz : z ∈ range (exhaustionChartMap F K d (ofLevel N)) := by
    rw [range_exhaustionChartMap]
    exact hN
  obtain ⟨x, hx⟩ := hz
  exact ⟨ofLevel N, x, hx⟩

/-! ## Invertible matrices -/

variable (γ γ' : Matrix.GeneralLinearGroup (Fin (d + 1)) F)

omit [ProperSpace F] [NeZero d] in
theorem entries_mul :
    entries (γ * γ') = fun k => Matrix.vecMul (entries γ k) (entries γ') := by
  funext k j
  simp [entries, Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem pullback_isActionPullback (U : ExhaustionIndex F K d) :
    IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) U (targetIndex K γ U)
      (pullback K γ U) :=
  pullback_coordinate K γ U

/-- The pullback along `γ'` followed by the pullback along `γ` is the pullback along `γ γ'`. -/
theorem isActionPullback_pullback_comp (U : ExhaustionIndex F K d) :
    IsActionPullback K (entries (γ * γ')) (entries_row_zero_ne_zero (γ * γ')) U
      (targetIndex K γ (targetIndex K γ' U))
      ((pullback K γ' U).comp (pullback K γ (targetIndex K γ' U))) :=
  (pullback_isActionPullback K γ' U).comp (pullback_isActionPullback K γ _) _
    (entries_mul γ γ')

/-- The chosen target of `U` lies in every member that receives a pullback of `U`. -/
theorem targetIndex_subset {U T : ExhaustionIndex F K d}
    {φ : BoundedAlgHom K (exhaustionChart F K d T.level).algebra
      (exhaustionChart F K d U.level).algebra}
    (hφ : IsActionPullback K (entries γ) (entries_row_zero_ne_zero γ) U T φ) :
    (targetIndex K γ U).1 ⊆ T.1 := by
  classical
  have hle : targetLevel K γ U ≤ T.level := by
    refine Nat.find_min' (exists_chartAction_subset K γ U) fun x => ?_
    rw [← hφ.chart_eq K x, T.exhaustion_level]
    exact mem_exhaustionChartMap K T _
  rw [← T.exhaustion_level]
  exact exhaustion_mono F K d hle

/-- `(γ γ') · z = γ · (γ' · z)`. -/
theorem actionMap_mul (z : Omega F K d) :
    actionMap K (γ * γ') z = actionMap K γ (actionMap K γ' z) := by
  obtain ⟨U, x, rfl⟩ := exists_exhaustionChartMap_eq K z
  apply Subtype.ext
  rw [actionMap_chart, ← chart_pullback K γ' U x, actionMap_chart,
    ← (pullback_isActionPullback K γ (targetIndex K γ' U)).chart_eq K]
  exact ((isActionPullback_pullback_comp K γ γ' U).chart_eq K x).symm

/-- The identity matrix acts trivially. -/
theorem actionMap_one (z : Omega F K d) : actionMap K 1 z = z := by
  obtain ⟨U, x, rfl⟩ := exists_exhaustionChartMap_eq K z
  apply Subtype.ext
  rw [actionMap_chart, ← (isActionPullback_id K U).chart_eq K x]
  exact congrArg (fun y => (exhaustionChartMap F K d U y).1)
    (BanachSpectrum.ext fun _ => rfl)

/-! ## Compatible strong maps and the action -/

theorem exhaustionAtlas_hasChainCharts : (exhaustionAtlas F K d).HasChainCharts := by
  intro (U : ExhaustionIndex F K d) (V : ExhaustionIndex F K d)
  rcases le_total U.level V.level with h | h
  · left
    refine (range_exhaustionChartMap_subset_iff F K d).2 ?_
    rw [← U.exhaustion_level, ← V.exhaustion_level]
    exact exhaustion_mono F K d h
  · right
    refine (range_exhaustionChartMap_subset_iff F K d).2 ?_
    rw [← U.exhaustion_level, ← V.exhaustion_level]
    exact exhaustion_mono F K d h

variable (F d) in
/-- Drinfeld's upper half space with its exhaustion atlas, as an object of the category of
compatible strong maps. -/
abbrev compatiblePresentation : CompatibleAtlasPresentation.{u, u, u} K :=
  ⟨exhaustionPresentation F K d⟩

/-- The compatible strong map `z ↦ γ · z`. -/
def compatibleHom : compatiblePresentation F K d ⟶ compatiblePresentation F K d :=
  AffinoidAtlasPresentation.CompatibleStrongHom.ofChain (presentationHom K γ)
    (exhaustionAtlas_hasChainCharts K)

@[simp]
theorem compatibleHom_baseMap : (compatibleHom K γ).baseMap = actionMap K γ := rfl

theorem compatibleHom_one :
    compatibleHom K (1 : Matrix.GeneralLinearGroup (Fin (d + 1)) F) =
      𝟙 (compatiblePresentation F K d) := by
  refine AffinoidAtlasPresentation.CompatibleStrongHom.ext_of_pullback
    (ContinuousMap.ext (actionMap_one K)) fun U => ?_
  have hU : (compatibleHom K 1).baseMap ''
        Set.range ((compatiblePresentation F K d).presentation.atlas.chart U) ⊆
      Set.range ((compatiblePresentation F K d).presentation.atlas.chart U) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (actionMap_one K _).symm⟩
  refine ⟨U, hU, ?_⟩
  have hs : (targetIndex K 1 U).1 ⊆ U.1 := targetIndex_subset K 1 (isActionPullback_id K U)
  refine (AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_upper _ _ U U hU
    ((range_exhaustionChartMap_subset_iff F K d).2 hs)).trans
      (Eq.trans ?_ ((exhaustionAtlas F K d).restriction_id U Subset.rfl).symm)
  exact ((pullback_isActionPullback K 1 U).comp_res hs).eq (isActionPullback_id K U)

theorem compatibleHom_mul :
    compatibleHom K (γ * γ') = compatibleHom K γ' ≫ compatibleHom K γ := by
  have hb : (compatibleHom K (γ * γ')).baseMap =
      (compatibleHom K γ' ≫ compatibleHom K γ).baseMap :=
    ContinuousMap.ext (actionMap_mul K γ γ')
  refine AffinoidAtlasPresentation.CompatibleStrongHom.ext_of_pullback hb fun U => ?_
  have hc := isActionPullback_pullback_comp K γ γ' U
  have hT : (compatibleHom K (γ * γ')).baseMap ''
        Set.range ((compatiblePresentation F K d).presentation.atlas.chart U) ⊆
      Set.range ((compatiblePresentation F K d).presentation.atlas.chart
        (targetIndex K γ (targetIndex K γ' U))) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨BanachSpectrum.comap ((pullback K γ' U).comp
      (pullback K γ (targetIndex K γ' U))).toBoundedRingHom x, Subtype.ext ?_⟩
    exact (hc.chart_eq K x).trans (actionMap_chart K (γ * γ') U x).symm
  refine ⟨targetIndex K γ (targetIndex K γ' U), hT, ?_⟩
  have hs : (targetIndex K (γ * γ') U).1 ⊆ (targetIndex K γ (targetIndex K γ' U)).1 :=
    targetIndex_subset K (γ * γ') hc
  have e₁ := AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_upper
    (presentationHom K (γ * γ')) (exhaustionAtlas_hasChainCharts K) U _ hT
    ((range_exhaustionChartMap_subset_iff F K d).2 hs)
  have e₂ := AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_selected
    (presentationHom K γ') (exhaustionAtlas_hasChainCharts K) U
  have e₃ := AffinoidAtlasPresentation.CompatibleStrongHom.ofChain_pullback_selected
    (presentationHom K γ) (exhaustionAtlas_hasChainCharts K) (targetIndex K γ' U)
  have e₄ := ((pullback_isActionPullback K (γ * γ') U).comp_res hs).eq hc
  have e₅ := AffinoidAtlasPresentation.CompatibleStrongHom.comp_pullback
    (compatibleHom K γ') (compatibleHom K γ) U (targetIndex K γ' U)
    (targetIndex K γ (targetIndex K γ' U)) ((presentationHom K γ').image_chart_subset U)
    ((presentationHom K γ).image_chart_subset _) (by rw [hb] at hT; exact hT)
  exact e₁.trans (e₄.trans ((congrArg₂ BoundedAlgHom.comp e₂ e₃).symm.trans e₅.symm))

/-- `γ ↦ (z ↦ γ · z)` as a monoid homomorphism into the endomorphisms of `Ω` among compatible
strong maps. -/
def compatibleAction :
    Matrix.GeneralLinearGroup (Fin (d + 1)) F →* End (compatiblePresentation F K d) where
  toFun := compatibleHom K
  map_one' := compatibleHom_one K
  map_mul' γ γ' := compatibleHom_mul K γ γ'

variable (F d) in
/-- Drinfeld's upper half space as an analytic space, with the action of `GL_{d+1}(F)`: the
image of `compatibleAction` in the localized category of analytic spaces. -/
def omegaAction : Action (SaturatedAtlasPresentation.LocalizedCategory.{u, u, u} (K := K))
    (Matrix.GeneralLinearGroup (Fin (d + 1)) F) :=
  ((CompatibleAtlasPresentation.saturationFunctor ⋙
    SaturatedAtlasPresentation.localizationFunctor).mapAction _).obj
      ⟨compatiblePresentation F K d, compatibleAction K⟩

theorem omegaAction_V : (omegaAction F K d).V = SaturatedAtlasPresentation.localizationFunctor.obj
    (SaturatedAtlasPresentation.ofSaturation (exhaustionPresentation F K d)) := rfl

theorem omegaAction_ρ : (omegaAction F K d).ρ γ =
    SaturatedAtlasPresentation.localizationFunctor.map
      (compatibleHom K γ).saturationExtension := rfl

/-- The underlying continuous map of the action of `γ` is `z ↦ γ · z`. -/
theorem localizedSpaceFunctor_map_omegaAction :
    SaturatedAtlasPresentation.localizedSpaceFunctor.map ((omegaAction F K d).ρ γ) =
      TopCat.ofHom (actionMap K γ) :=
  SaturatedAtlasPresentation.localizedSpaceFunctor_map _

instance : T2Space (SaturatedAtlasPresentation.localizedSpaceFunctor.obj (omegaAction F K d).V) :=
  inferInstanceAs (T2Space (Omega F K d))

end DrinfeldUpperHalfSpace

end Langlands.Analytic
