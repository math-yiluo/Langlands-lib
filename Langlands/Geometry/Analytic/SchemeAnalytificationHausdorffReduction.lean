import Langlands.Geometry.Analytic.SchemeAnalytificationSpace
import Mathlib.Topology.Separation.Hausdorff

/-! # Hausdorffness detected on pairs of affine analytic charts -/

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The equality relation in the glued space is closed on each pair of affine
analytic charts, with the product topology on their source spaces. -/
def ChartRelationClosed : Prop :=
  ∀ U V : X.affineOpens,
    IsClosed {p : LocalSpace K f U × LocalSpace K f V | ι K f U p.1 = ι K f V p.2}

/-- When the canonical charts are open maps, Hausdorffness of the actual glued
space is equivalent to closedness of their pairwise equality relations. -/
theorem t2Space_iff_chartRelationClosed
    (hopen : ∀ U : X.affineOpens, IsOpenMap (ι K f U)) :
    T2Space (Space K f) ↔ ChartRelationClosed K f := by
  constructor
  · intro h
    let := h
    intro U V
    exact isClosed_eq ((ι K f U).continuous.comp continuous_fst)
      ((ι K f V).continuous.comp continuous_snd)
  · intro h
    refine ⟨?_⟩
    intro a b hab
    obtain ⟨U, x, rfl⟩ := exists_ι K f a
    obtain ⟨V, y, rfl⟩ := exists_ι K f b
    obtain ⟨s, t, hs, ht, hxs, hyt, hst⟩ :=
      isOpen_prod_iff.mp (h U V).isOpen_compl x y hab
    refine ⟨ι K f U '' s, ι K f V '' t, hopen U _ hs, hopen V _ ht,
      ⟨x, hxs, rfl⟩, ⟨y, hyt, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro z ⟨x', hx', hxz⟩ ⟨y', hy', hyz⟩
    have hne : ι K f U x' ≠ ι K f V y' :=
      hst (show (x', y') ∈ s ×ˢ t from ⟨hx', hy'⟩)
    exact hne (hxz.trans hyz.symm)

end Langlands.Analytic.SchemeAnalytification
