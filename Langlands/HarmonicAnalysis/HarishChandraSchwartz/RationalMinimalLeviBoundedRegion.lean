import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviHeight

/-! # Uniform bounds on bounded-`H₀` subsets of the actual minimal Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- Every bounded-`H₀` subset of the full minimal Levi is contained in a compact set in
the canonical rational-point topology. Closedness of the subset is not required. -/
def HasMinimalLeviCompactSublevels (N : Seminorm ℝ (RealTorusSpace.V S)) : Prop :=
  ∀ R : ℝ, ∃ Q : Set (standardLeviPoints i ν ∅), IsCompact Q ∧
    ∀ m : standardLeviPoints i ν ∅, N (rationalMinimalH0 hG hi hν m) ≤ R → m ∈ Q

/-- A closed matrix embedding and the proved height comparison give compact containment
of all bounded-`H₀` subsets, without requiring continuity of `H₀`. -/
theorem hasMinimalLeviCompactSublevels_of_heightComparison
    (N : Seminorm ℝ (RealTorusSpace.V S))
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) (hheight : HasMinimalLeviHeightComparison hG hi hν N ρ) :
    HasMinimalLeviCompactSublevels hG hi hν N := by
  obtain ⟨C, hC, hb⟩ := hheight
  intro R
  refine ⟨{m : standardLeviPoints i ν ∅ |
    rationalHeight (F := F) ρ (m : rationalPoints G) ≤ C * (1 + R)}, ?_, ?_⟩
  · exact (isClosed_standardLeviPoints i ν ∅).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_rationalHeight_le ρ hρ (C * (1 + R)))
  · intro m hm
    have h := (hb m).trans (mul_le_mul_of_nonneg_left (add_le_add_right hm 1) hC.le)
    change rationalHeight (F := F) ρ (m : rationalPoints G) ≤ C * (1 + R)
    linarith

/-- The actual minimal-Levi structural covering gives the compact containment needed in
the bounded-region step of positive-part decay. -/
theorem hasMinimalLeviCompactSublevels_of_cartanCovering
    [LocallyOfFiniteType G.X.hom]
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) :
    HasMinimalLeviCompactSublevels hG hi hν N :=
  hasMinimalLeviCompactSublevels_of_heightComparison hG hi hν N ρ hρ
    (hasMinimalLeviHeightComparison_of_cartanCovering hG hi hν hK0 hcover N hN ρ)

/-- A jointly continuous family with compact parameter space is uniformly bounded by any
continuous positive weight on every bounded-`H₀` subset of the actual minimal Levi. This is a
topological bounded-region lemma; realization of these continuity premises is separate. -/
theorem HasMinimalLeviCompactSublevels.exists_norm_le_weight
    {N : Seminorm ℝ (RealTorusSpace.V S)}
    (hcompact : HasMinimalLeviCompactSublevels hG hi hν N)
    {κ : Type*} [TopologicalSpace κ] [CompactSpace κ]
    {Φ : κ → standardLeviPoints i ν ∅ → ℂ}
    (hΦ : Continuous (Function.uncurry Φ)) {B : standardLeviPoints i ν ∅ → ℝ}
    (hB : Continuous B) (hBpos : ∀ m, 0 < B m) (R : ℝ) :
    ∃ C > 0, ∀ ω m, N (rationalMinimalH0 hG hi hν m) ≤ R → ‖Φ ω m‖ ≤ C * B m := by
  obtain ⟨Q, hQ, hsub⟩ := hcompact R
  let f : κ × standardLeviPoints i ν ∅ → ℝ := fun p => ‖Φ p.1 p.2‖ / B p.2
  have hf : Continuous f :=
    hΦ.norm.div (hB.comp continuous_snd) fun p => (hBpos p.2).ne'
  obtain ⟨b, hb⟩ := (isCompact_univ.prod hQ).bddAbove_image hf.continuousOn
  refine ⟨max b 1, zero_lt_one.trans_le (le_max_right _ _), fun ω m hm => ?_⟩
  have hp : (ω, m) ∈ (Set.univ : Set κ) ×ˢ Q := ⟨Set.mem_univ _, hsub m hm⟩
  have h : f (ω, m) ≤ max b 1 := (hb ⟨(ω, m), hp, rfl⟩).trans (le_max_left _ _)
  exact (div_le_iff₀ (hBpos m)).mp h

end Langlands.HarishChandraSchwartz
