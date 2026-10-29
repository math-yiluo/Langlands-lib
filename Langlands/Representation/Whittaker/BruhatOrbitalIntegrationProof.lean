import Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Group.GL.UpperUnipotentFactorizationProof
import Langlands.Group.GL.CompactOpen

/-!
# Proof of orbital integration onto test functions on an upper Bruhat cell

This module proves `Langlands.Whittaker.BruhatOrbitalIntegrationStatement`. The published
cell coordinates `U × H × U_w⁻ ≃ₜ C` give a continuous section `s` of the torus map `π`,
and the published factorization `U_w⁺ × U_w⁻ ≃ₜ U` gives a continuous plus coordinate
`q : M → U_w⁺` with `m = q m • s (π m)` and `q (u • s c) = u`. The orbital integral is the
raw fiber average along the section. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Topology Filter

namespace Langlands.Whittaker

open Langlands.GeneralLinear HarmonicAnalysis

universe uK uF

section Tube

/-- Integrating out the second variable of a locally constant function on a product, whose
second-variable support lies in one compact set, gives a locally constant function. -/
theorem isLocallyConstant_integral_of_isCompact {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {mY : MeasurableSpace Y} (ν : Measure Y) {g : X × Y → ℂ}
    (hg : IsLocallyConstant g) {T : Set Y} (hT : IsCompact T)
    (hzero : ∀ x y, y ∉ T → g (x, y) = 0) :
    IsLocallyConstant fun x => ∫ y, g (x, y) ∂ν := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
  have hN : IsOpen {q : X × Y | g q - g (x₀, q.2) = 0} :=
    (hg.comp₂ (hg.comp_continuous (continuous_const.prodMk continuous_snd))
      (· - ·)).isOpen_fiber 0
  obtain ⟨u, v, hu, -, hxu, hTv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x₀)) hT hN
    (by
      rintro ⟨a, b⟩ ⟨ha, -⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      simp)
  filter_upwards [hu.mem_nhds (hxu (Set.mem_singleton x₀))] with x hx
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ T
  · exact sub_eq_zero.mp (huv ⟨hx, hTv hy⟩)
  · show g (x, y) = g (x₀, y)
    rw [hzero x y hy, hzero x₀ y hy]

/-- The indicator of a clopen set with a constant value is locally constant. -/
theorem isLocallyConstant_indicator_const {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsClopen s) (k : ℂ) : IsLocallyConstant (s.indicator fun _ => k) := by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  by_cases hx : x ∈ s
  · filter_upwards [hs.isOpen.mem_nhds hx] with y hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

end Tube

section Coordinates

variable {r : ℕ} {K : Type uK} [Field K] [TopologicalSpace K] {w : Equiv.Perm (Fin r)}

/-- The section of the torus map given by the cell coordinates:
`s c = (u₁, d, v)` where `eT (u₁, d, v) = c` and `v ∈ U_w⁻` is viewed in `U`. -/
def cellSection
    (eT : (upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) ≃ₜ
      UpperBruhatCell r K w) (c : UpperBruhatCell r K w) :
    upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K :=
  ((eT.symm c).1, (eT.symm c).2.1,
    Subgroup.inclusion (permutationUnipotentMinus_le_upperUnipotent r K w) (eT.symm c).2.2)

/-- The plus coordinate `u⁺` of the last factor `u₂ = u⁺ * u⁻`. -/
def plusCoordinate
    (e : (permutationUnipotentPlus r K w × permutationUnipotentMinus r K w) ≃ₜ
      upperUnipotent r K)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    permutationUnipotentPlus r K w :=
  (e.symm m.2.2).1

variable
    {eT : (upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) ≃ₜ
      UpperBruhatCell r K w}
    {e : (permutationUnipotentPlus r K w × permutationUnipotentMinus r K w) ≃ₜ
      upperUnipotent r K}

theorem continuous_cellSection : Continuous (cellSection eT) := by
  refine (continuous_fst.comp eT.symm.continuous).prodMk
    ((continuous_fst.comp (continuous_snd.comp eT.symm.continuous)).prodMk ?_)
  exact (continuous_subtype_val.comp
    (continuous_snd.comp (continuous_snd.comp eT.symm.continuous))).subtype_mk _

theorem continuous_plusCoordinate : Continuous (plusCoordinate e) :=
  continuous_fst.comp (e.symm.continuous.comp (continuous_snd.comp continuous_snd))

/-- `π ∘ s = id`. -/
theorem upperBruhatTorusMap_cellSection
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (c : UpperBruhatCell r K w) :
    upperBruhatTorusMap r w (cellSection eT c) = c := by
  apply Subtype.ext
  rw [upperBruhatTorusMap_val]
  conv_rhs => rw [← eT.apply_symm_apply c]
  rw [heT]
  rfl

/-- On points whose last factor lies in `U_w⁻`, the section recovers the point. -/
theorem cellSection_upperBruhatTorusMap
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (x : upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) :
    cellSection eT (upperBruhatTorusMap r w (x.1, x.2.1,
        Subgroup.inclusion (permutationUnipotentMinus_le_upperUnipotent r K w) x.2.2)) =
      (x.1, x.2.1,
        Subgroup.inclusion (permutationUnipotentMinus_le_upperUnipotent r K w) x.2.2) := by
  have h : upperBruhatTorusMap r w (x.1, x.2.1,
      Subgroup.inclusion (permutationUnipotentMinus_le_upperUnipotent r K w) x.2.2) = eT x := by
    apply Subtype.ext
    rw [upperBruhatTorusMap_val, heT]
    rfl
  rw [h, cellSection, eT.symm_apply_apply]

/-- The plus coordinate of `u • s c` is `u`. -/
theorem plusCoordinate_bruhatFiberAct_cellSection
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    (u : permutationUnipotentPlus r K w) (c : UpperBruhatCell r K w) :
    plusCoordinate e (bruhatFiberAct r K w u (cellSection eT c)) = u := by
  have h : (bruhatFiberAct r K w u (cellSection eT c)).2.2 = e (u, (eT.symm c).2.2) := by
    apply Subtype.ext
    rw [bruhatFiberAct_snd_snd_val, he]
    rfl
  rw [plusCoordinate, h, e.symm_apply_apply]

/-- Every point is the plus coordinate acting on the section of its image:
`m = q m • s (π m)`. -/
theorem bruhatFiberAct_plusCoordinate_cellSection
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    bruhatFiberAct r K w (plusCoordinate e m) (cellSection eT (upperBruhatTorusMap r w m)) =
      m := by
  obtain ⟨x, hx⟩ : ∃ x, e.symm m.2.2 = x := ⟨_, rfl⟩
  have hm : m.2.2.val = x.1.val * x.2.val := by
    rw [← he, ← hx, e.apply_symm_apply]
  have hq : plusCoordinate e m = x.1 := by
    rw [plusCoordinate, hx]
  have hy : bruhatFiberAct r K w x.1⁻¹ m =
      ((bruhatFiberAct r K w x.1⁻¹ m).1, (bruhatFiberAct r K w x.1⁻¹ m).2.1,
        Subgroup.inclusion (permutationUnipotentMinus_le_upperUnipotent r K w) x.2) := by
    refine Prod.ext rfl (Prod.ext rfl (Subtype.ext ?_))
    rw [bruhatFiberAct_snd_snd_val, hm, InvMemClass.coe_inv, inv_mul_cancel_left]
    rfl
  have hπ : upperBruhatTorusMap r w m =
      upperBruhatTorusMap r w (bruhatFiberAct r K w x.1⁻¹ m) :=
    (upperBruhatTorusMap_bruhatFiberAct _ m).symm
  rw [hq, hπ, hy, cellSection_upperBruhatTorusMap heT
    ((bruhatFiberAct r K w x.1⁻¹ m).1, (bruhatFiberAct r K w x.1⁻¹ m).2.1, x.2), ← hy,
    bruhatFiberAct_bruhatFiberAct, mul_inv_cancel, bruhatFiberAct_one]

/-- The orbit map from the trivialized product, `(c, u) ↦ u • s c`, is continuous. -/
theorem continuous_bruhatFiberAct_cellSection [IsTopologicalRing K] :
    Continuous fun q : UpperBruhatCell r K w × permutationUnipotentPlus r K w =>
      bruhatFiberAct r K w q.2 (cellSection eT q.1) :=
  (continuous_bruhatFiberAct r K w).comp
    (f := fun q : UpperBruhatCell r K w × permutationUnipotentPlus r K w =>
      (q.2, cellSection eT q.1))
    (continuous_snd.prodMk (continuous_cellSection.comp continuous_fst))

end Coordinates

section Average

variable {r : ℕ} {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {w : Equiv.Perm (Fin r)}
variable (μ : letI := borel (permutationUnipotentPlus r K w)
  Measure (permutationUnipotentPlus r K w))
variable [IsFiniteMeasureOnCompacts μ]
variable
    {eT : (upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) ≃ₜ
      UpperBruhatCell r K w}
    {e : (permutationUnipotentPlus r K w × permutationUnipotentMinus r K w) ≃ₜ
      upperUnipotent r K}

variable (eT) in
/-- The raw fiber average read on the cell through the coordinate section. -/
def cellAverage
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)) :
    UpperBruhatCell r K w → ℂ :=
  fun c => bruhatFiberAverage r K w μ α (cellSection eT c)

/-- The descended average satisfies Shalika's formula (1.11) at every point. -/
theorem cellAverage_upperBruhatTorusMap
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    (hμ : letI := borel (permutationUnipotentPlus r K w); μ.IsMulRightInvariant)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) :
    cellAverage μ eT α (upperBruhatTorusMap r w m) = bruhatFiberAverage r K w μ α m := by
  conv_rhs => rw [← bruhatFiberAct_plusCoordinate_cellSection heT he m]
  rw [bruhatFiberAverage_bruhatFiberAct r K w μ hμ]
  rfl

/-- The nonzero set of the descended average lies in `π '' tsupport α`. -/
theorem support_cellAverage_subset
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)) :
    Function.support (cellAverage μ eT α) ⊆
      upperBruhatTorusMap r w '' tsupport (α : _ → ℂ) := by
  intro c hc
  obtain ⟨u, hu⟩ := exists_bruhatFiberAct_mem_tsupport_of_mem_support r K w μ
    (m := cellSection eT c) hc
  exact ⟨_, hu, by rw [upperBruhatTorusMap_bruhatFiberAct, upperBruhatTorusMap_cellSection heT]⟩

theorem tsupport_cellAverage_subset
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)) :
    tsupport (cellAverage μ eT α) ⊆ upperBruhatTorusMap r w '' tsupport (α : _ → ℂ) :=
  closure_minimal (support_cellAverage_subset μ heT α)
    ((α.hasCompactSupport.isCompact.image (continuous_upperBruhatTorusMap r w)).isClosed)

theorem hasCompactSupport_cellAverage
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)) :
    HasCompactSupport (cellAverage μ eT α) :=
  (α.hasCompactSupport.isCompact.image (continuous_upperBruhatTorusMap r w)).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_cellAverage_subset μ heT α)

theorem isLocallyConstant_cellAverage
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K)) :
    IsLocallyConstant (cellAverage μ eT α) := by
  refine isLocallyConstant_integral_of_isCompact μ
    (g := fun q : UpperBruhatCell r K w × permutationUnipotentPlus r K w =>
      α (bruhatFiberAct r K w q.2 (cellSection eT q.1)))
    (α.locallyConstant.comp_continuous continuous_bruhatFiberAct_cellSection)
    (α.hasCompactSupport.isCompact.image (continuous_plusCoordinate (e := e))) ?_
  intro c u hu
  by_contra h
  apply hu
  rw [← plusCoordinate_bruhatFiberAct_cellSection he u c]
  exact ⟨_, subset_tsupport _ h, rfl⟩

/-- The orbital integral as a complex-linear map between test-function spaces. -/
def cellOrbitalIntegral
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (he : ∀ x, (e x).val = x.1.val * x.2.val) :
    SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) →ₗ[ℂ]
      SchwartzBruhat (UpperBruhatCell r K w) where
  toFun α := ⟨cellAverage μ eT α, isLocallyConstant_cellAverage μ he α,
    hasCompactSupport_cellAverage μ heT α⟩
  map_add' α β := by
    apply Subtype.ext
    funext c
    simp [cellAverage, map_add]
  map_smul' a α := by
    apply Subtype.ext
    funext c
    simp [cellAverage, map_smul]

theorem cellOrbitalIntegral_apply
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
    (c : UpperBruhatCell r K w) :
    cellOrbitalIntegral μ heT he α c = cellAverage μ eT α c :=
  rfl

end Average

section Main

variable {r : ℕ} {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {w : Equiv.Perm (Fin r)}

/-- The generic form of the statement: given the cell coordinates, the unipotent
factorization and a nonempty compact open subset `K₀` of `U_w⁺`, every right-invariant Haar
measure on `U_w⁺` has exactly one orbital integration map with the three properties. -/
theorem existsUnique_bruhatOrbitalIntegration
    (eT : (upperUnipotent r K × (Fin r → Kˣ) × permutationUnipotentMinus r K w) ≃ₜ
      UpperBruhatCell r K w)
    (heT : ∀ x, (eT x).val =
      x.1.val * permutation r K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val)
    (e : (permutationUnipotentPlus r K w × permutationUnipotentMinus r K w) ≃ₜ
      upperUnipotent r K)
    (he : ∀ x, (e x).val = x.1.val * x.2.val)
    {K₀ : Set (permutationUnipotentPlus r K w)} (hK₀c : IsCompact K₀) (hK₀o : IsOpen K₀)
    (hK₀ : K₀.Nonempty) :
    letI := borel (permutationUnipotentPlus r K w)
    ∀ (μ : Measure (permutationUnipotentPlus r K w)) [Measure.IsHaarMeasure μ]
      [μ.IsMulRightInvariant],
      ∃! I : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K) →ₗ[ℂ]
          SchwartzBruhat (UpperBruhatCell r K w),
        (∀ (α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K))
            (m : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K),
          I α (upperBruhatTorusMap r w m) = bruhatFiberAverage r K w μ α m) ∧
        Function.Surjective I ∧
        (∀ α : SchwartzBruhat (upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K),
          tsupport (I α : UpperBruhatCell r K w → ℂ) ⊆
            upperBruhatTorusMap r w '' tsupport (α : _ → ℂ)) := by
  let _ : MeasurableSpace (permutationUnipotentPlus r K w) := borel _
  have : BorelSpace (permutationUnipotentPlus r K w) := ⟨rfl⟩
  intro μ _ hμ
  refine ⟨cellOrbitalIntegral μ heT he,
    ⟨fun α m => cellAverage_upperBruhatTorusMap μ heT he hμ α m, ?_,
      fun α => tsupport_cellAverage_subset μ heT α⟩, ?_⟩
  · -- Surjectivity: lift `f` to `m ↦ f (π m) * φ (q m)` with `φ` a normalized indicator.
    intro f
    have hreal : μ.real K₀ ≠ 0 :=
      (measureReal_ne_zero_iff hK₀c.measure_ne_top).2 (hK₀o.measure_ne_zero μ hK₀)
    let φ : permutationUnipotentPlus r K w → ℂ := K₀.indicator fun _ => ((μ.real K₀ : ℂ))⁻¹
    let g : upperUnipotent r K × (Fin r → Kˣ) × upperUnipotent r K → ℂ :=
      fun m => f (upperBruhatTorusMap r w m) * φ (plusCoordinate e m)
    have hg_lc : IsLocallyConstant g :=
      (f.locallyConstant.comp_continuous (continuous_upperBruhatTorusMap r w)).mul
        ((isLocallyConstant_indicator_const ⟨hK₀c.isClosed, hK₀o⟩ _).comp_continuous
          continuous_plusCoordinate)
    have hg_cs : HasCompactSupport g := by
      refine HasCompactSupport.intro ((f.hasCompactSupport.isCompact.prod hK₀c).image
        (continuous_bruhatFiberAct_cellSection (eT := eT))) fun m hm => ?_
      by_contra h
      apply hm
      refine ⟨(upperBruhatTorusMap r w m, plusCoordinate e m), ⟨?_, ?_⟩,
        bruhatFiberAct_plusCoordinate_cellSection heT he m⟩
      · exact subset_tsupport _ (left_ne_zero_of_mul h)
      · by_contra hq
        exact h (by simp only [g, φ, Set.indicator_of_notMem hq, mul_zero])
    refine ⟨⟨g, hg_lc, hg_cs⟩, Subtype.ext (funext fun c => ?_)⟩
    have hint : ∀ u : permutationUnipotentPlus r K w,
        g (bruhatFiberAct r K w u (cellSection eT c)) = f c * φ u := fun u => by
      simp only [g, upperBruhatTorusMap_bruhatFiberAct, upperBruhatTorusMap_cellSection heT,
        plusCoordinate_bruhatFiberAct_cellSection he]
    show ∫ u, g (bruhatFiberAct r K w u (cellSection eT c)) ∂μ = f c
    simp only [hint]
    rw [integral_const_mul, integral_indicator_const _ hK₀o.measurableSet, Complex.real_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hreal), mul_one]
  · -- Uniqueness: `J α c = J α (π (s c)) = avg α (s c)`.
    rintro J ⟨hJ, -, -⟩
    refine LinearMap.ext fun α => Subtype.ext (funext fun c => ?_)
    have h := hJ α (cellSection eT c)
    rw [upperBruhatTorusMap_cellSection heT c] at h
    exact h

end Main

/-- Shalika's orbital integration onto test functions on the actual upper Bruhat cell
(Lemma 1.10 with formula (1.11)) over every canonical p-adic field. -/
theorem bruhatOrbitalIntegration : BruhatOrbitalIntegrationStatement.{uF} := by
  intro p _ F
  let _ := F.canonicalNormedField
  intro n w
  obtain ⟨-, eT, heT⟩ := upperBruhatCoordinates F.Carrier (n + 1) w
  obtain ⟨e, he⟩ := upperUnipotentFactorization F.Carrier (n + 1) w
  obtain ⟨L, hLc, -⟩ := F.canonicalGeneralLinearCompactOpen (n + 1) Set.univ Filter.univ_mem
  have hLc' : IsCompact (L : Set (GeneralLinear (n + 1) F.Carrier)) := hLc
  have hLo : IsOpen (L : Set (GeneralLinear (n + 1) F.Carrier)) := L.isOpen
  let K₀ : Set (permutationUnipotentPlus (n + 1) F.Carrier w) :=
    Subtype.val ⁻¹' (L : Set (GeneralLinear (n + 1) F.Carrier))
  have hK₀c : IsCompact K₀ :=
    (isClosed_permutationUnipotentPlus (n + 1) F.Carrier w).isClosedEmbedding_subtypeVal.isCompact_preimage
      hLc'
  have hK₀o : IsOpen K₀ := hLo.preimage continuous_subtype_val
  have hK₀ : K₀.Nonempty := ⟨1, L.one_mem⟩
  exact existsUnique_bruhatOrbitalIntegration eT heT e he hK₀c hK₀o hK₀

end Langlands.Whittaker
