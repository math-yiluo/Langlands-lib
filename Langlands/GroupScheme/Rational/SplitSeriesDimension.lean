import Langlands.GroupScheme.Rational.SplitSeriesUnipotent
import Langlands.GroupScheme.Rational.VectorGroupDimension
import Langlands.GroupScheme.Rational.FppfQuotientSmooth

/-! # Intrinsic dimension of affine split-unipotent groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

/-- An affine connected group with a finite Ga-series is smooth of relative
dimension equal to its series length. -/
theorem HasSplitSeries.smoothOfRelativeDimension {n : ℕ}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (h : HasSplitSeries n H) : SmoothOfRelativeDimension n H.X.hom := by
  induction n generalizing H with
  | zero => exact h.isVectorGroupOfDimension_zero.smoothOfRelativeDimension
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, _, hcK, _, hq, hV, hK⟩ := h
    let : IsClosedImmersion j.hom.hom.left := hj
    let : Mono j.hom.hom := Over.mono_of_mono_left _
    let : IsAffineHom K.X.hom := hj.isAffineHom
    let : ConnectedSpace K.X.left := hcK
    let : IsAffineHom V.X.hom := hV.isAffineHom
    let : QuasiCompact (q.hom.hom.left ≫ V.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ V.X.hom
    let hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
      ⟨inferInstance, rfl⟩
    let : SmoothOfRelativeDimension n q.hom.hom.left :=
      hq.smoothOfRelativeDimension_of_kernel hjrep (ih hK)
    let : SmoothOfRelativeDimension 1 V.X.hom := hV.smoothOfRelativeDimension
    rw [← Over.w q.hom.hom]
    infer_instance

/-- All finite Ga-series on an affine connected group have the same length. -/
theorem HasSplitSeries.length_eq {m n : ℕ}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (hm : HasSplitSeries m H) (hn : HasSplitSeries n H) : m = n :=
  relativeDimension_eq H.X.hom hm.smoothOfRelativeDimension hn.smoothOfRelativeDimension

/-- The dimension selected by a finite Ga-series witness. For affine connected
groups, the following lemmas identify this with every series length and with
the actual smooth relative dimension. -/
def IsSplitUnipotent.dimension
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (h : IsSplitUnipotent H) : ℕ :=
  h.choose

theorem IsSplitUnipotent.hasSplitSeries_dimension
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (h : IsSplitUnipotent H) : HasSplitSeries h.dimension H :=
  h.choose_spec

/-- The selected dimension is the actual smooth relative dimension. -/
theorem IsSplitUnipotent.smoothOfRelativeDimension
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (h : IsSplitUnipotent H) : SmoothOfRelativeDimension h.dimension H.X.hom :=
  h.hasSplitSeries_dimension.smoothOfRelativeDimension

/-- Any other series computes the selected dimension. -/
theorem IsSplitUnipotent.dimension_eq_of_hasSplitSeries {n : ℕ}
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (h : IsSplitUnipotent H) (hn : HasSplitSeries n H) : h.dimension = n :=
  h.hasSplitSeries_dimension.length_eq hn

/-- Dimension zero is exactly triviality on every scheme test. -/
theorem IsSplitUnipotent.dimension_eq_zero_iff
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (h : IsSplitUnipotent H) :
    h.dimension = 0 ↔ SubgroupFunctor.range (𝟙 H) = ⊥ := by
  constructor
  · intro hd
    simpa only [hd, HasSplitSeries] using h.hasSplitSeries_dimension
  · intro ht
    exact h.dimension_eq_of_hasSplitSeries ht

/-- A nontrivial affine connected split-unipotent group has positive dimension. -/
theorem IsSplitUnipotent.dimension_pos_of_range_ne_bot
    {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (h : IsSplitUnipotent H) (ht : SubgroupFunctor.range (𝟙 H) ≠ ⊥) :
    0 < h.dimension :=
  Nat.pos_of_ne_zero (fun hd => ht (h.dimension_eq_zero_iff.mp hd))

section Quotient

variable {N H Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom N.X.hom] [ConnectedSpace N.X.left]
    [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    {j : N ⟶ H} {q : H ⟶ Q}
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q)
    (hj : (SubgroupFunctor.range j).IsRepresentedBy j)
    (hN : IsSplitUnipotent N) (hH : IsSplitUnipotent H) (hQ : IsSplitUnipotent Q)

include hq hj in
/-- Smooth relative dimensions make series lengths additive for an actual
represented fppf quotient of affine connected split-unipotent groups. -/
theorem IsSplitUnipotent.dimension_eq_add_of_fppfQuotient :
    hH.dimension = hN.dimension + hQ.dimension := by
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let : SmoothOfRelativeDimension hN.dimension q.hom.hom.left :=
    hq.smoothOfRelativeDimension_of_kernel hj hN.smoothOfRelativeDimension
  let : SmoothOfRelativeDimension hQ.dimension Q.X.hom := hQ.smoothOfRelativeDimension
  have hsum : SmoothOfRelativeDimension (hN.dimension + hQ.dimension) H.X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  exact relativeDimension_eq H.X.hom hH.smoothOfRelativeDimension hsum

include hq hj hN in
/-- A nontrivial represented split-unipotent kernel strictly decreases the
intrinsic dimension of the given quotient. -/
theorem IsSplitUnipotent.dimension_lt_of_fppfQuotient
    (ht : SubgroupFunctor.range (𝟙 N) ≠ ⊥) : hQ.dimension < hH.dimension := by
  have heq := IsSplitUnipotent.dimension_eq_add_of_fppfQuotient hq hj hN hH hQ
  have hp := hN.dimension_pos_of_range_ne_bot ht
  omega

end Quotient

end Langlands.GroupScheme.RelativeRoot
