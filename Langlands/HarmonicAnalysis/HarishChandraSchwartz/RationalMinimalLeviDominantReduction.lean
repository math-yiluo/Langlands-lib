import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviHeight

/-! # Compact reduction of the full minimal-Levi chamber to dominant uniformizer points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

theorem minimalLeviUniformizer_add (y z : cocharacterLattice S) :
    minimalLeviUniformizer (i := i) (ν := ν) (y + z) =
      minimalLeviUniformizer (i := i) (ν := ν) y *
        minimalLeviUniformizer (i := i) (ν := ν) z := by
  simp only [minimalLeviUniformizer, ofAdd_add, map_mul]

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- Every point of the full actual minimal-Levi closed chamber is a dominant uniformizer
point multiplied on both sides by elements of a single compact subset of the minimal Levi. -/
def HasCompactDominantMinimalLeviReduction : Prop :=
  ∃ Q : Set (standardLeviPoints i ν ∅), IsCompact Q ∧
    ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
      ∃ k₁ ∈ Q, ∃ k₂ ∈ Q, ∃ y : cocharacterLattice S,
        (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) ∧
        m = k₁ * minimalLeviUniformizer (i := i) (ν := ν) y * k₂

set_option maxHeartbeats 600000 in
/-- The existing empty-index Levi Cartan covering yields compact dominant reduction on the
entire minimal-Levi closed chamber. No Xi upper or lower estimate is used. -/
theorem hasCompactDominantMinimalLeviReduction_of_cartanCovering
    [LocallyOfFiniteType G.X.hom]
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0) :
    HasCompactDominantMinimalLeviReduction hG hi hν := by
  classical
  obtain ⟨F0, hcover⟩ := hcover
  let f0 : centralizerPoints i → standardLeviPoints i ν ∅ := fun f =>
    ⟨f, by rw [standardLeviPoints_empty_eq_centralizerPoints hG hi hν]; exact f.2⟩
  let R := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν |>.toFinset
  obtain ⟨b, hb⟩ := ((R.product F0).image fun p : characterLattice S × centralizerPoints i =>
    RealTorusSpace.eval S p.1 (rationalMinimalH0 hG hi hν (f0 p.2))).exists_le
  obtain ⟨N, hN⟩ := exists_nat_ge b
  let c : cocharacterLattice S := N • ν
  have hshift : ∀ α ∈ simpleRelativeRoots i ν, ∀ f ∈ F0,
      RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν (f0 f)) ≤
        (latticePairing S α c : ℝ) := by
    intro α hα f hf
    have hαR : α ∈ R := by simpa [R] using hα
    have hpair : (α, f) ∈ R.product F0 := Finset.mem_product.mpr ⟨hαR, hf⟩
    have hbound := hb _ (Finset.mem_image_of_mem _ hpair)
    have hαν : (1 : ℝ) ≤ latticePairing S α ν := by
      have hpos := (simpleRelativeRoots_subset_positive i ν hα).2
      exact_mod_cast (show (1 : ℤ) ≤ latticePairing S α ν by omega)
    have hmul := mul_le_mul_of_nonneg_left hαν (Nat.cast_nonneg (α := ℝ) N)
    calc RealTorusSpace.eval S α (rationalMinimalH0 hG hi hν (f0 f))
        ≤ b := hbound
      _ ≤ N := hN
      _ ≤ (latticePairing S α c : ℝ) := by
        simpa only [c, map_nsmul, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_one] using hmul
  let Q0 : Set (standardLeviPoints i ν ∅) := {m | (m : rationalPoints G) ∈ K0}
  have hQ0 : IsCompact Q0 :=
    (isClosed_standardLeviPoints i ν ∅).isClosedEmbedding_subtypeVal.isCompact_preimage hK0
  let Q1 : Set (standardLeviPoints i ν ∅) :=
    ⋃ f ∈ F0, (fun k : standardLeviPoints i ν ∅ =>
      k * f0 f * minimalLeviUniformizer (i := i) (ν := ν) (-c)) '' Q0
  have hQ1 : IsCompact Q1 :=
    F0.isCompact_biUnion fun f _ =>
      hQ0.image ((continuous_id.mul continuous_const).mul continuous_const)
  refine ⟨Q0 ∪ Q1, hQ0.union hQ1, fun m hm => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hmeq⟩ := hcover m m.2
  obtain ⟨y, rfl⟩ := ha.1
  change (m : rationalPoints G) =
    k₁ * (f : rationalPoints G) * Langlands.Aubert.General.uniformizerPowers i y * k₂ at hmeq
  let m₁ : standardLeviPoints i ν ∅ := ⟨k₁, hk₁.2⟩
  let m₂ : standardLeviPoints i ν ∅ := ⟨k₂, hk₂.2⟩
  have h₁ : rationalMinimalH0 hG hi hν m₁ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₁.1
  have h₂ : rationalMinimalH0 hG hi hν m₂ = 0 :=
    rationalMinimalH0_eq_zero_of_mem_compact hG hi hν hK0 hk₂.1
  have hm' : m = m₁ * f0 f * minimalLeviUniformizer (i := i) (ν := ν) y.toAdd * m₂ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_minimalLeviUniformizer]
    exact hmeq
  have hH : rationalMinimalH0 hG hi hν m =
      rationalMinimalH0 hG hi hν (f0 f) + (1 : ℝ) ⊗ₜ[ℤ] y.toAdd := by
    rw [hm']
    simp only [rationalMinimalH0_mul, h₁, h₂, rationalMinimalH0_minimalLeviUniformizer,
      zero_add, add_zero]
  refine ⟨m₁ * f0 f * minimalLeviUniformizer (i := i) (ν := ν) (-c),
    Or.inr (Set.mem_iUnion₂.mpr ⟨f, hf, ⟨m₁, hk₁.1, rfl⟩⟩),
    m₂, Or.inl hk₂.1, y.toAdd + c, ?_, ?_⟩
  · intro α hα
    have hdom := hm α hα
    rw [hH, map_add, RealTorusSpace.eval_tmul, one_mul] at hdom
    have h := hshift α hα f hf
    have hc : (0 : ℝ) ≤ (latticePairing S α (y.toAdd + c) : ℝ) := by
      simp only [map_add, Int.cast_add]
      linarith
    exact_mod_cast hc
  · have hw : minimalLeviUniformizer (i := i) (ν := ν) y.toAdd =
        minimalLeviUniformizer (i := i) (ν := ν) (-c) *
          minimalLeviUniformizer (i := i) (ν := ν) (y.toAdd + c) := by
      rw [← minimalLeviUniformizer_add]
      congr 1
      abel
    rw [hm', hw]
    group

end Langlands.HarishChandraSchwartz
