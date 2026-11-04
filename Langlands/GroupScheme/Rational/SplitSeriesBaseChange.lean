import Langlands.GroupScheme.Rational.VectorCoordinatesBaseChange
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.GeometricConnectedness

/-! # Scalar extension of represented split series -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k] (L : Type u) [Field L] [Algebra k L]

/-- Natural all-test vector coordinates remain vector coordinates after any
extension of the ground field, with the same dimension. -/
theorem IsVectorGroupOfDimension.baseChange
    {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (h : IsVectorGroupOfDimension V n) :
    IsVectorGroupOfDimension ((GroupScheme.baseChange (algebraBaseMap k L)).obj V) n := by
  obtain ⟨e, he⟩ := h
  have he' : IsNaturalVectorCoordinates e := he
  exact ⟨vectorBaseChangeCoordinates e L, IsNaturalVectorCoordinates.baseChange he'⟩

/-- A finite represented normal Ga-series over a field stays such a series,
of the same length, after an arbitrary extension of that field. -/
theorem HasSplitSeries.baseChange
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    {n : ℕ} (h : HasSplitSeries n H) :
    HasSplitSeries n ((GroupScheme.baseChange (algebraBaseMap k L)).obj H) := by
  induction n generalizing H with
  | zero =>
    change SubgroupFunctor.range (𝟙 _) = ⊥
    rw [← CategoryTheory.Functor.map_id (GroupScheme.baseChange (algebraBaseMap k L)),
      SubgroupFunctor.range_baseChangeHom, h, SubgroupFunctor.bot_baseChange]
  | succ n ih =>
    obtain ⟨K, V, j, q, hj, hs, hc, hn, hq, hv, hk⟩ := h
    let b := algebraBaseMap k L
    let : IsClosedImmersion j.hom.hom.left := hj
    let : IsAffineHom K.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    let : Smooth K.X.hom := hs
    let : ConnectedSpace K.X.left := hc
    have hsL : Smooth ((GroupScheme.baseChange b).obj K).X.hom := by
      change Smooth (pullback.snd K.X.hom b)
      infer_instance
    have hcL : ConnectedSpace ((GroupScheme.baseChange b).obj K).X.left :=
      K.connectedSpace_baseChange_of_smooth_affine b
    refine ⟨(GroupScheme.baseChange b).obj K, (GroupScheme.baseChange b).obj V,
      (GroupScheme.baseChange b).map j, (GroupScheme.baseChange b).map q,
      hj.baseChange b, hsL, hcL, ?_, ?_, hv.baseChange L, ih hk⟩
    · rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange b
    · simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b

/-- Split unipotence in the represented-series sense is preserved by every
field extension. -/
theorem IsSplitUnipotent.baseChange
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (h : IsSplitUnipotent H) :
    IsSplitUnipotent ((GroupScheme.baseChange (algebraBaseMap k L)).obj H) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.baseChange L⟩

/-- Retain the length of a supplied represented split series while extending
its actual group, inclusions and quotient maps to the new field. -/
def baseChangeSplitSeries
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (s : {n : ℕ // HasSplitSeries n H}) :
    {n : ℕ // HasSplitSeries n ((GroupScheme.baseChange (algebraBaseMap k L)).obj H)} :=
  ⟨s.val, s.property.baseChange L⟩

@[simp]
theorem baseChangeSplitSeries_length
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (s : {n : ℕ // HasSplitSeries n H}) :
    (baseChangeSplitSeries L s).val = s.val := rfl

end Langlands.GroupScheme.RelativeRoot
