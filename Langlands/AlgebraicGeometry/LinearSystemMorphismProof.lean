import Langlands.AlgebraicGeometry.LinearSystemMorphismStatement
import Langlands.AlgebraicGeometry.LinearSystem.Morphism
import Langlands.AlgebraicGeometry.LinearSystem.DualNumberPoints

/-! # Proof of the linear system morphism statement

The morphism is `LinearSystem.linearSystemMap`, glued from the chart maps on the
nonvanishing loci `U_j` of the sections. For a rational point `x ∈ U_j`, the ratios
`s i / s j` at `x` are scalars `α i`, and `s i - α i • s j` vanishes at `x`. A second rational
point, or a tangent vector at `x`, along which all these combinations vanish lands in `U_j`
and has the same ratios, hence the same image. Conversely two points of `U_j` with the same
image have the same ratios and so are cut out by the same linear combinations.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

noncomputable section

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
  {L : LineBundle X} {n : ℕ} {s : Fin (n + 1) → GlobalSections L.obj}

/-- At a rational point of `U_j`, each `s i - α i • s j` vanishes for suitable scalars
`α i`, namely the values of the ratios `s i / s j`. -/
lemma exists_vanishesAlong_basisDiff {x : Spec (CommRingCat.of K) ⟶ X} (hx : x ≫ p = 𝟙 _)
    {j : Fin (n + 1)} (hxj : ∀ τ, x τ ∈ trivializationOpen L.obj (s j)) :
    ∃ α : Fin (n + 1) → K, ∀ i, VanishesAlong L x (linComb p s (basisDiff i j (α i))) := by
  choose α hα using fun i ↦ exists_scalarsFromBase_eq p hx (sectionRatio L x (s i) (s j))
  exact ⟨α, fun i ↦ (vanishesAlong_linComb_basisDiff_iff p s hxj i (α i)).mpr (hα i).symm⟩

variable (hs : ∀ x : X, ∃ i, x ∈ nonvanishingLocus L.obj (s i))
include hs

/-- A field-valued point along which every `s k - α k • s j` vanishes lies in `U_j`. -/
lemma mem_of_vanishesAlong_basisDiff {K' : Type u} [Field K']
    {y : Spec (CommRingCat.of K') ⟶ X} {j : Fin (n + 1)} {α : Fin (n + 1) → K}
    (hy : ∀ k, VanishesAlong L y (linComb p s (basisDiff k j (α k)))) :
    y (IsLocalRing.closedPoint K') ∈ trivializationOpen L.obj (s j) := by
  by_contra hmem
  obtain ⟨k, hk⟩ := exists_mem_trivializationOpen hs (y (IsLocalRing.closedPoint K'))
  have hyk : ∀ τ, y τ ∈ trivializationOpen L.obj (s k) := fun τ ↦ by
    rwa [Subsingleton.elim τ (IsLocalRing.closedPoint K')]
  have h0 := (vanishesAlong_iff_sectionRatio_eq_zero hyk _).mp (hy k)
  rw [sectionRatio_linComb_basisDiff p s hyk, sectionRatio_self hyk,
    (vanishesAlong_iff_sectionRatio_eq_zero hyk _).mp ((vanishesAlong_iff_not_mem y (s j)).mpr hmem),
    mul_zero, sub_zero] at h0
  have h10 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K')).hom h0
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

end Langlands.AlgebraicGeometry.LinearSystem

namespace Langlands.AlgebraicGeometry

open LinearSystem

/-- Base-point-free sections define a morphism to projective space whose fibres on rational
points and rational tangent vectors are described by vanishing of linear combinations. -/
theorem linearSystemMorphism : LinearSystemMorphismStatement.{u} := by
  intro K _ X p L n s hs
  refine ⟨linearSystemMap p hs, linearSystemMap_toSpec p hs, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs (x (IsLocalRing.closedPoint K))
    have hxj := forall_mem_of_mem hj
    constructor
    · intro H c
      have hyj : ∀ τ, y τ ∈ trivializationOpen L.obj (s j) := by
        apply forall_mem_of_mem
        apply mem_trivializationOpen_of_comp_mem p hs y j
        rw [← H]
        exact comp_mem_coordinateOpen p hs hxj _
      exact (vanishesAlong_linComb_iff_of_comp_eq p hs hxj hyj H c).mp
    · intro H
      obtain ⟨α, hα⟩ := exists_vanishesAlong_basisDiff p hx hxj
      have hyα : ∀ k, VanishesAlong L y (linComb p s (basisDiff k j (α k))) :=
        fun k ↦ H _ (hα k)
      have hyj := forall_mem_of_mem (mem_of_vanishesAlong_basisDiff p hs hyα)
      refine comp_eq_of_sectionRatio_eq p hs hxj hyj (hx.trans hy.symm) fun i ↦ ?_
      rw [(vanishesAlong_linComb_basisDiff_iff p s hxj i (α i)).mp (hα i),
        (vanishesAlong_linComb_basisDiff_iff p s hyj i (α i)).mp (hyα i), hx, hy]
  · intro x t hx ht
    obtain ⟨j, hj⟩ := exists_mem_trivializationOpen hs (x (IsLocalRing.closedPoint K))
    have hxj := forall_mem_of_mem hj
    have htj := forall_mem_of_augmentation_comp ht.2 hj
    have hx'j : ∀ τ, (dualNumberProjection K ≫ x) τ ∈ trivializationOpen L.obj (s j) :=
      fun τ ↦ by rw [Scheme.Hom.comp_apply]; exact hxj _
    have hp : t ≫ p = (dualNumberProjection K ≫ x) ≫ p := by
      rw [ht.1, Category.assoc, hx, Category.comp_id]
    constructor
    · intro H c hc
      exact (vanishesAlong_linComb_iff_of_comp_eq p hs htj hx'j H c).mpr
        (vanishesAlong_comp _ hc)
    · intro H
      obtain ⟨α, hα⟩ := exists_vanishesAlong_basisDiff p hx hxj
      refine comp_eq_of_sectionRatio_eq p hs htj hx'j hp fun i ↦ ?_
      rw [(vanishesAlong_linComb_basisDiff_iff p s htj i (α i)).mp (H _ (hα i)),
        (vanishesAlong_linComb_basisDiff_iff p s hx'j i (α i)).mp
          (vanishesAlong_comp _ (hα i)), hp]

end Langlands.AlgebraicGeometry
