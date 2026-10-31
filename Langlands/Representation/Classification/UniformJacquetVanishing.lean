import Langlands.Representation.Classification.SegmentEdgeFactorHypotheses
import Langlands.Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof
import Langlands.Representation.CuspidalSupport.JacquetSubquotientProof

/-! Jacquet vanishing along shapes with a block not divisible by the cuspidal rank. -/

noncomputable section

namespace Langlands.Classification

open GeneralLinear Geometric CuspidalSupport

universe uF uV

section Blocks

/-- Association with a refinement preserves divisibility of all block sizes. -/
theorem dvd_target_size_of_conjugatesLevi_flatten {K : Type*} [Field K]
    {n r : ℕ} {B D : BlockShape n} (hB : ∀ i, r ∣ B.size i)
    (S : BlockRefinement D) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := K) B (D.flatten S) w) (j : Fin D.length) :
    r ∣ D.size j := by
  rw [← (S j).sum_eq]
  apply Finset.dvd_sum
  intro k _
  obtain ⟨i, hi⟩ := TotalConjugatingCount.blockMap_surjective hw
    (D.flattenBlockEquiv S ⟨j, k⟩)
  have hs : (S j).size k = B.size i := by
    rw [← D.flatten_size_flattenBlockEquiv S ⟨j, k⟩, ← hi]
    exact TotalConjugatingCount.size_blockMap hw i
  rw [hs]
  exact hB i

/-- A target block not divisible by the source block divisor rules out every
associated standard refinement of the target. -/
theorem no_associated_refinement_of_not_dvd {K : Type*} [Field K]
    {n r : ℕ} {B D : BlockShape n} (hB : ∀ i, r ∣ B.size i)
    (hD : ∃ j, ¬ r ∣ D.size j) :
    ¬ ∃ (S : BlockRefinement D) (w : Equiv.Perm (Fin n)),
      (B.leviSubgroup K).map (MulAut.conj (permutation n K w)).toMonoidHom =
        (refinedLevi K D S).map (D.leviEmbedding K) := by
  rintro ⟨S, w, hw⟩
  rw [SegmentEdge.refinedLevi_map_eq_flatten_leviSubgroup] at hw
  obtain ⟨j, hj⟩ := hD
  exact hj (dvd_target_size_of_conjugatesLevi_flatten hB S w hw j)

end Blocks

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An actual smooth object has zero Jacquet module along every shape with
a block not divisible by the specified rank. -/
def NondivisibleJacquetVanishing {n : ℕ} (r : ℕ)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) : Prop :=
  letI := T.topology
  ∀ D : BlockShape n, (∃ j, ¬ r ∣ D.size j) →
    Subsingleton ((T.normalizedJacquetFunctor D).obj π)

/-- Quasicuspidal induction has zero Jacquet module whenever some target
block size is not divisible by a common divisor of the source block sizes. -/
theorem jacquet_induction_subsingleton_of_not_dvd {n r : ℕ}
    (B D : BlockShape n) (hB : ∀ i, r ∣ B.size i) (hD : ∃ j, ¬ r ∣ D.size j) :
    letI := T.topology
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      IsLeviQuasicuspidal B ρ.representation →
      Subsingleton ((T.normalizedJacquetFunctor D).obj
        ((T.normalizedParabolicInductionFunctor B).obj ρ)) := by
  let := T.topology
  intro ρ hρ
  exact quasicuspidalJacquetVanishing F T n B D ρ hρ
    (no_associated_refinement_of_not_dvd hB hD)

/-- The same vanishing holds for every actual smooth subquotient of the
quasicuspidal induction. -/
theorem subquotient_jacquet_subsingleton_of_not_dvd {n r : ℕ}
    (B D : BlockShape n) (hB : ∀ i, r ∣ B.size i) (hD : ∃ j, ¬ r ∣ D.size j) :
    letI := T.topology
    ∀ (ρ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
      IsLeviQuasicuspidal B ρ.representation →
      ∀ Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
        SmoothRep.IsSubquotient Z ((T.normalizedParabolicInductionFunctor B).obj ρ) →
        Subsingleton ((T.normalizedJacquetFunctor D).obj Z) := by
  let := T.topology
  intro ρ hρ Z hZ
  let := jacquet_induction_subsingleton_of_not_dvd T B D hB hD ρ hρ
  exact subsingleton_of_isSubquotient
    (normalizedJacquetSubquotient.{uF, max uF uV} p F T n D _ Z hZ)

/-- Specialization to products of actual supercuspidal block factors. -/
theorem supercuspidal_product_subquotient_jacquet_subsingleton_of_not_dvd {n r : ℕ}
    (hn : 0 < n) (B D : BlockShape n) (hB : ∀ i, r ∣ B.size i)
    (hD : ∃ j, ¬ r ∣ D.size j) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := B.size i))
      (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      SmoothRep.IsSubquotient Z
        ((T.normalizedProductInductionFunctor B).obj (fun i => (A i).obj)) →
      Subsingleton ((T.normalizedJacquetFunctor D).obj Z) := by
  let := T.topology
  intro A Z hZ
  exact subquotient_jacquet_subsingleton_of_not_dvd T B D hB hD
    (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    (glCuspidalTensor.{uV, uF} p F T n hn B A).2.2 Z hZ

/-- Every actual subquotient of the increasing induction of a segment has
zero Jacquet module along any shape with a block not divisible by its rank. -/
theorem segment_induction_subquotient_jacquet_subsingleton_of_not_dvd
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (D : BlockShape (m * r))
    (hD : ∃ j, ¬ r ∣ D.size j) :
    letI := T.topology
    ∀ (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
      (Z : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m * r) F.Carrier)),
      SmoothRep.IsSubquotient Z (T.segmentInduced A.obj m hr) →
      Subsingleton ((T.normalizedJacquetFunctor D).obj Z) := by
  let := T.topology
  intro A Z hZ
  let factors : ∀ i : Fin (BlockShape.uniform m r hr).length,
      SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (BlockShape.uniform m r hr).size i) :=
    fun i => SupercuspidalRep.twist (T.determinantPowerCharacter r ((i : ℕ) : ℝ))
      (T.isOpen_ker_determinantPowerCharacter r ((i : ℕ) : ℝ))
      (T.ker_determinant_le_ker_determinantPowerCharacter r ((i : ℕ) : ℝ)) A
  exact supercuspidal_product_subquotient_jacquet_subsingleton_of_not_dvd T
    (Nat.mul_pos hm hr) (BlockShape.uniform m r hr) D (fun _ => dvd_refl r) hD
    factors Z hZ

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- An actual segment subrepresentation has zero Jacquet module along a
shape with a block not divisible by the segment's cuspidal rank. -/
theorem IsSegmentSubrepresentation.jacquet_subsingleton_of_not_dvd
    {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π) (D : BlockShape Δ.degree)
    (hD : ∃ j, ¬ Δ.rank ∣ D.size j) :
    letI := T.topology
    Subsingleton ((T.normalizedJacquetFunctor D).obj π) := by
  let := T.topology
  obtain ⟨A, _, _, j, hj⟩ := hπ
  exact segment_induction_subquotient_jacquet_subsingleton_of_not_dvd T
    Δ.length_pos Δ.rank_pos D hD A π
    (SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩)

/-- An actual segment socle has zero Jacquet module along a shape with a
block not divisible by the segment's cuspidal rank. -/
theorem IsSegmentSocle.jacquet_subsingleton_of_not_dvd
    {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) (D : BlockShape Δ.degree)
    (hD : ∃ j, ¬ Δ.rank ∣ D.size j) :
    letI := T.topology
    Subsingleton ((T.normalizedJacquetFunctor D).obj π) :=
  hπ.isSegmentSubrepresentation.jacquet_subsingleton_of_not_dvd T D hD

/-- A segment socle satisfies nondivisible Jacquet vanishing at its
cuspidal rank, simultaneously for all target shapes. -/
theorem IsSegmentSocle.nondivisibleJacquetVanishing
    {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) :
    NondivisibleJacquetVanishing T Δ.rank π := by
  let := T.topology
  intro D hD
  exact hπ.jacquet_subsingleton_of_not_dvd T D hD

end Langlands.PadicField.TopologicalData
