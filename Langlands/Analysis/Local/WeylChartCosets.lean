import Langlands.Analysis.Local.WeylChartDecomposition

/-! # Cosets of the torus near the identity -/

set_option linter.unusedSectionVars false

noncomputable section

namespace Langlands.Analysis.WeylChart

open Metric Set Topology MeasureTheory Measure Langlands.QuotientIntegration
open scoped NNReal ENNReal

universe u v

section Ext

/-- Two finite Borel measures on a second countable ultrametric space that agree on all
closed balls of positive radius and on the whole space are equal. -/
theorem measure_ext_of_closedBall {X : Type*} [MetricSpace X] [IsUltrametricDist X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ]
    (h : ∀ (x : X) (ρ : ℝ), 0 < ρ → μ (closedBall x ρ) = ν (closedBall x ρ))
    (huniv : μ univ = ν univ) : μ = ν := by
  let S : Set (Set X) := {s | ∃ (x : X) (ρ : ℝ), 0 < ρ ∧ s = closedBall x ρ}
  have hbasis : TopologicalSpace.IsTopologicalBasis S := by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨x, ρ, hρ, rfl⟩
      exact IsUltrametricDist.isOpen_closedBall x hρ.ne'
    · intro x U hx hU
      obtain ⟨ρ, hρ, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
      exact ⟨closedBall x ρ, ⟨x, ρ, hρ, rfl⟩, mem_closedBall_self hρ.le, hsub⟩
  have hpi : IsPiSystem S := by
    rintro _ ⟨x, ρ, hρ, rfl⟩ _ ⟨y, σ, hσ, rfl⟩ hne
    rcases IsUltrametricDist.closedBall_subset_trichotomy (x := x) (y := y) (r := ρ) (s := σ)
      with hs | hs | hs
    · rw [inter_eq_left.mpr hs]
      exact ⟨x, ρ, hρ, rfl⟩
    · rw [inter_eq_right.mpr hs]
      exact ⟨y, σ, hσ, rfl⟩
    · exact (hne.not_disjoint hs).elim
  refine ext_of_generate_finite S (BorelSpace.measurable_eq.trans hbasis.borel_eq_generateFrom)
    hpi ?_ huniv
  rintro _ ⟨x, ρ, hρ, rfl⟩
  exact h x ρ hρ

end Ext

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F] [IsUltrametricDist F]
  [ProperSpace F]
  {R : Type v} [NormedRing R] [NormedAlgebra F R] [FiniteDimensional F R] [CompleteSpace R]
  [IsUltrametricDist R] [MeasurableSpace R] [BorelSpace R]

theorem unitOf_one : unitOf (1 : R) = 1 :=
  Units.ext (val_unitOf isUnit_one)

section Cosets

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)
  (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

/-- An element of the torus ball is the unit of a small central coordinate. -/
theorem exists_torusUnit_eq (h : torusGroup γ) (hh : h ∈ torusBall hγ hr) :
    ∃ s : centralizerAlg F γ, ‖s‖ ≤ r ∧ torusUnit (F := F) γ s = h := by
  have hv := (mem_torusBall_iff hγ hr h).1 hh
  refine ⟨torusValue (F := F) γ h - 1, by simpa [mem_closedBall, dist_eq_norm] using hv, ?_⟩
  apply (isEmbedding_torusValue (F := F) γ).injective
  rw [torusValue_torusUnit hγ hr (by simpa [mem_closedBall, dist_eq_norm] using hv)]
  abel

theorem cosetChart_injOn :
    InjOn (cosetChart (F := F) γ) (closedBall 0 r) := by
  intro y hy y' hy' h
  rw [mem_closedBall, dist_zero_right] at hy hy'
  set u := unitOf (1 + (y : R))
  set u' := unitOf (1 + (y' : R))
  have hrel : u'⁻¹ * u ∈ torusGroup γ := by
    have := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using this
  have hK : u'⁻¹ * u ∈ unitBall hγ hr :=
    (unitBall hγ hr).mul_mem ((unitBall hγ hr).inv_mem (unitOf_transverse_mem hγ hr hy'))
      (unitOf_transverse_mem hγ hr hy)
  obtain ⟨s, hs, hsu⟩ := exists_torusUnit_eq hγ hr hbij ⟨_, hrel⟩ hK
  have hprod : unitOf (1 + ((y, (0 : centralizerAlg F γ)).1 : R)) *
      unitOf (1 + ((y, (0 : centralizerAlg F γ)).2 : R)) =
      unitOf (1 + ((y', s).1 : R)) * unitOf (1 + ((y', s).2 : R)) := by
    have hsu' : unitOf (1 + (s : R)) = u'⁻¹ * u := congrArg Subtype.val hsu
    change unitOf (1 + (y : R)) * unitOf (1 + ((0 : centralizerAlg F γ) : R)) =
      unitOf (1 + (y' : R)) * unitOf (1 + (s : R))
    rw [hsu', ZeroMemClass.coe_zero, add_zero, unitOf_one, mul_one, mul_inv_cancel_left]
  have hx : ‖((y, (0 : centralizerAlg F γ)) : Coord F γ)‖ ≤ r := by
    rw [Prod.norm_def, norm_zero]
    exact max_le hy hr.pos.le
  have hx' : ‖((y', s) : Coord F γ)‖ ≤ r := by
    rw [Prod.norm_def]
    exact max_le hy' hs
  exact congrArg Prod.fst (eq_of_unitOf_mul_unitOf_eq hγ hr hbij hx hx' hprod)

/-- The coset of an element of the coordinate subgroup is the coset chart of the
transverse coordinate of its inverse. -/
theorem leftQuotientMap_eq_cosetChart (k : Rˣ) (hk : k ∈ unitBall hγ hr) :
    ∃ x : Coord F γ, ‖x‖ ≤ r ∧ k⁻¹ = unitOf (1 + (x.1 : R)) * unitOf (1 + (x.2 : R)) ∧
      leftQuotientMap (torusGroup γ) k = cosetChart γ x.1 := by
  obtain ⟨x, hx, hkx⟩ := exists_eq_unitOf_mul_unitOf hγ hr hbij k⁻¹
    ((unitBall hγ hr).inv_mem hk)
  refine ⟨x, hx, hkx, ?_⟩
  have hk' : k = (unitOf (1 + (x.2 : R)))⁻¹ * (unitOf (1 + (x.1 : R)))⁻¹ := by
    rw [← mul_inv_rev, ← hkx, inv_inv]
  rw [hk', cosetChart]
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ?_
  simpa [mul_inv_rev] using unitOf_mem_torusGroup x.2

end Cosets

section Images

/-- The product of the transverse and central units of a coordinate. -/
def unitMap (γ : Rˣ) (x : Coord F γ) : Rˣ :=
  unitOf (1 + (x.1 : R)) * unitOf (1 + (x.2 : R))

variable {γ : Rˣ} (hγ : IsRegularPosition F γ) {r : ℝ} (hr : IsSmallRadius hγ r)

include hr in
theorem continuousOn_unitMap : ContinuousOn (unitMap (F := F) γ) (closedBall 0 r) := by
  have h1 : ContinuousOn (fun x : Coord F γ => unitOf (1 + (x.1 : R))) (closedBall 0 r) := by
    refine continuousOn_unitOf.comp (by fun_prop) fun x hx => ?_
    have hx1 : ‖x.1‖ ≤ r := (norm_fst_le x).trans (by simpa using hx)
    obtain ⟨u, hu⟩ := isUnit_one_add_transverse hγ hr hx1
    exact ⟨u, hu⟩
  have h2 : ContinuousOn (fun x : Coord F γ => unitOf (1 + (x.2 : R))) (closedBall 0 r) := by
    refine continuousOn_unitOf.comp (by fun_prop) fun x hx => ?_
    have hx2 : ‖x.2‖ ≤ r := (norm_snd_le x).trans (by simpa using hx)
    obtain ⟨u, hu⟩ := isUnit_one_add_central hγ hr hx2
    exact ⟨u, hu⟩
  exact h1.mul h2

include hr in
theorem val_unitMap {x : Coord F γ} (hx : x ∈ closedBall 0 r) :
    ((unitMap (F := F) γ x : Rˣ) : R) = 1 + productMap γ x :=
  val_unitOf_mul_unitOf hγ hr (by simpa using hx)

variable (hbij : BijOn (productMap (F := F) γ) (closedBall 0 r) (coordCLE hγ '' closedBall 0 r))
include hr hbij

/-- The product map sends relatively open subsets of the coordinate ball to open sets. -/
theorem isOpen_image_productMap {O : Set (Coord F γ)} (hO : IsOpen O)
    (hOB : O ⊆ closedBall 0 r) : IsOpen (productMap (F := F) γ '' O) := by
  have : CompactSpace (closedBall (0 : Coord F γ) r) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hcont : Continuous (fun x : closedBall (0 : Coord F γ) r => productMap γ x.val) := by
    unfold productMap
    fun_prop
  have hinj : Function.Injective (fun x : closedBall (0 : Coord F γ) r => productMap γ x.val) :=
    fun a b h => Subtype.ext (hbij.injOn a.property b.property h)
  have hemb := hcont.isClosedEmbedding hinj
  obtain ⟨V, hV, hVO⟩ := (hemb.isInducing.isOpen_iff).1 (hO.preimage continuous_subtype_val)
  have himage : productMap (F := F) γ '' O =
      range (fun x : closedBall (0 : Coord F γ) r => productMap γ x.val) ∩ V := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨⟨x, hOB hx⟩, rfl⟩, ?_⟩
      have : (⟨x, hOB hx⟩ : closedBall (0 : Coord F γ) r) ∈
          (fun x : closedBall (0 : Coord F γ) r => productMap γ x.val) ⁻¹' V := by
        rw [hVO]
        exact hx
      exact this
    · rintro ⟨⟨x, rfl⟩, hz⟩
      have : x ∈ (Subtype.val : closedBall (0 : Coord F γ) r → Coord F γ) ⁻¹' O := by
        rw [← hVO]
        exact hz
      exact ⟨x.val, this, rfl⟩
  have hrange : range (fun x : closedBall (0 : Coord F γ) r => productMap γ x.val) =
      coordCLE hγ '' closedBall 0 r := by
    rw [← hbij.image_eq]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [himage, hrange]
  exact ((coordCLE hγ).toHomeomorph.isOpenMap _
    (IsUltrametricDist.isOpen_closedBall 0 hr.pos.ne')).inter hV

/-- The unit map sends relatively open subsets of the coordinate ball to open sets. -/
theorem isOpen_image_unitMap {O : Set (Coord F γ)} (hO : IsOpen O)
    (hOB : O ⊆ closedBall 0 r) : IsOpen (unitMap (F := F) γ '' O) := by
  have hP := isOpen_image_productMap hγ hr hbij hO hOB
  have hval : unitMap (F := F) γ '' O =
      Units.val ⁻¹' ((fun z : R => 1 + z) '' (productMap (F := F) γ '' O)) := by
    ext k
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨productMap γ x, ⟨x, hx, rfl⟩, (val_unitMap hγ hr (hOB hx)).symm⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, hk⟩
      exact ⟨x, hx, Units.ext ((val_unitMap hγ hr (hOB hx)).trans hk)⟩
  rw [hval]
  exact ((Homeomorph.addLeft (1 : R)).isOpenMap _ hP).preimage Units.continuous_val

end Images

end Langlands.Analysis.WeylChart
