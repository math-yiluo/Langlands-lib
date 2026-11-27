import Langlands.BaseChange.TwistedCharacter.CompactOpenHaarChart
import Langlands.BaseChange.TwistedLocalDescent.SupNormRing

/-! # Haar measure on compact open subgroups in additive coordinates

A Haar measure restricted to a compact open subgroup is its mass times the image of the
normalized Haar measure of the subgroup. Over an ultrametric proper nontrivially normed field,
for a compact open subgroup `K(r)` of `GL_n` whose image under `g ↦ g − 1` is the closed matrix
ball of radius `r` (a congruence ball `{g : ‖g − 1‖ ≤ r}`), the image under `g ↦ g` (as a matrix)
of Haar measure restricted to `K(r)` is a constant multiple of additive Haar measure restricted
to the ball `closedBall 1 r`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Langlands.HarishChandraSchwartz Topology Langlands
open scoped ENNReal NNReal

universe u v

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
/-- A Haar measure restricted to a compact open subgroup is the mass of the subgroup times the
image of its normalized Haar measure. -/
theorem restrict_eq_smul_map_normalizedHaar (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    [CompactSpace K] (hKo : IsOpen (K : Set G)) [MeasurableSpace K] [BorelSpace K] :
    μ.restrict (K : Set G) = μ K • (normalizedHaar K).map Subtype.val := by
  have hKc : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  have : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  have hemb : MeasurableEmbedding (Subtype.val : K → G) :=
    hKo.isOpenEmbedding_subtypeVal.measurableEmbedding
  let ρ := μ.comap (Subtype.val : K → G)
  have hρ : ρ univ = μ K := by
    change μ.comap Subtype.val univ = μ K
    rw [hemb.comap_apply, image_univ, Subtype.range_coe]
  have : IsFiniteMeasure ρ := ⟨hρ ▸ hKc.measure_lt_top⟩
  have : ρ.IsMulLeftInvariant := by
    constructor
    intro h
    ext1 s hs
    change (μ.comap Subtype.val).map (h * ·) s = (μ.comap Subtype.val) s
    rw [map_apply (measurable_const_mul h) hs, hemb.comap_apply, hemb.comap_apply]
    have himg : Subtype.val '' ((h * ·) ⁻¹' s) = (fun x : G => (h : G) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨h * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨h⁻¹ * y, by simpa using hy, ?_⟩
        simp [hyx]
    rw [himg, measure_preimage_mul]
  have hhaar : ρ = μ K • normalizedHaar K := by
    simpa only [TopologicalSpace.PositiveCompacts.coe_top, normalizedHaar, hρ]
      using haarMeasure_unique ρ ⊤
  have hres : μ.restrict (K : Set G) = ρ.map Subtype.val := by
    change _ = (μ.comap Subtype.val).map Subtype.val
    rw [hemb.map_comap, Subtype.range_coe]
  rw [hres, hhaar, Measure.map_smul]
  exact hemb.measurable.aemeasurable

end Group

section Congruence

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]
  [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]

/-- **Haar measure on a congruence ball in additive coordinates.** -/
theorem map_val_restrict_congruenceBall (μG : Measure (GeneralLinear n 𝕂))
    [μG.IsHaarMeasure] (ν : Measure (Matrix (Fin n) (Fin n) 𝕂)) [ν.IsAddHaarMeasure]
    (U : OpenSubgroup (GeneralLinear n 𝕂)) [CompactSpace U] {r : ℝ}
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r) :
    (μG.restrict (U : Set (GeneralLinear n 𝕂))).map Units.val =
      (μG U * (ν (closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r))⁻¹) •
        ν.restrict (closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r) := by
  let _ : MeasurableSpace U := borel U
  have _ : BorelSpace U := ⟨rfl⟩
  have hrange' : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val) =
      closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r := by
    ext X
    constructor
    · rintro ⟨g, rfl⟩
      have : (g : GeneralLinear n 𝕂).val - 1 ∈ closedBall (0 : Matrix _ _ 𝕂) r :=
        hrange ▸ ⟨g, rfl⟩
      rwa [mem_closedBall_zero_iff, ← dist_eq_norm] at this
    · intro hX
      have : X - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r := by
        rwa [mem_closedBall_zero_iff, ← dist_eq_norm]
      rw [← hrange] at this
      obtain ⟨g, hg⟩ := this
      exact ⟨g, sub_left_injective hg⟩
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) 𝕂) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → 𝕂))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) 𝕂) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝕂))
  have : SecondCountableTopology (GeneralLinear n 𝕂) :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : CompactSpace U.toSubgroup := ‹CompactSpace U›
  let _ : MeasurableSpace U.toSubgroup := borel U.toSubgroup
  have _ : BorelSpace U.toSubgroup := ⟨rfl⟩
  have hopen : IsOpenEmbedding (fun g : U.toSubgroup =>
      ((U.toSubgroup.subtype g : GeneralLinear n 𝕂) : Matrix (Fin n) (Fin n) 𝕂)) :=
    Units.isOpenEmbedding_val.comp U.isOpen.isOpenEmbedding_subtypeVal
  have h1 := restrict_eq_smul_map_normalizedHaar μG U.toSubgroup U.isOpen
  have h2 := map_normalizedHaar_eq_restrict_of_units (H := U.toSubgroup) U.toSubgroup.subtype
    hopen ν
  have hr : (Set.range fun g : U.toSubgroup =>
      ((U.toSubgroup.subtype g : GeneralLinear n 𝕂) : Matrix (Fin n) (Fin n) 𝕂)) =
      closedBall (1 : Matrix (Fin n) (Fin n) 𝕂) r := hrange'
  rw [hr] at h2
  change Measure.map Units.val (μG.restrict (U.toSubgroup : Set (GeneralLinear n 𝕂))) = _
  rw [h1, Measure.map_smul, Measure.map_map Units.continuous_val.measurable
    continuous_subtype_val.measurable]
  change μG U.toSubgroup • Measure.map (fun g : U.toSubgroup =>
    ((U.toSubgroup.subtype g : GeneralLinear n 𝕂) : Matrix (Fin n) (Fin n) 𝕂))
    (normalizedHaar U.toSubgroup) = _
  rw [h2, smul_smul]
  rfl
  exact Units.continuous_val.measurable.aemeasurable

end Congruence

end Langlands.BaseChange.TwistedLocalDescent
