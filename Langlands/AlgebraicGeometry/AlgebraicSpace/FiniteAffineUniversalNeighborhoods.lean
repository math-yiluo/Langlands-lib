import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenSubfunctorDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenSubfunctors
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionRepresentability

/-! # Universal open neighborhoods from a finite map with AF source -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineUniversalNeighborhoods

open OpenSubfunctorLifting

variable {S : Scheme.{u}} {F : Presheaf S} {U T : Over S}
variable {π : (schemeYoneda S).obj U ⟶ F}

/-- The actual scheme representing the source over a test of a finite map. -/
def sourceOverTest (hπ : IsFinite π) (a : (schemeYoneda S).obj T ⟶ F) : Over S :=
  hπ.representable.pullback a

/-- Projection from the represented source to the original source scheme. -/
def sourceProjection (hπ : IsFinite π) (a : (schemeYoneda S).obj T ⟶ F) :
    sourceOverTest hπ a ⟶ U :=
  (schemeYoneda S).preimage (hπ.representable.fst a)

/-- Projection from the represented source to the test scheme. -/
def testProjection (hπ : IsFinite π) (a : (schemeYoneda S).obj T ⟶ F) :
    sourceOverTest hπ a ⟶ T :=
  hπ.representable.snd a

theorem sourceOverTest_square (hπ : IsFinite π)
    (a : (schemeYoneda S).obj T ⟶ F) :
    IsPullback ((schemeYoneda S).map (sourceProjection hπ a))
      ((schemeYoneda S).map (testProjection hπ a)) π a := by
  change IsPullback ((schemeYoneda S).map
    ((schemeYoneda S).preimage (hπ.representable.fst a))) _ π a
  rw [Functor.map_preimage]
  exact hπ.representable.isPullback a

theorem testProjection_isFinite (hπ : IsFinite π)
    (a : (schemeYoneda S).obj T ⟶ F) :
    _root_.AlgebraicGeometry.IsFinite (testProjection hπ a).left :=
  hπ.projection a _ _ (sourceOverTest_square hπ a)

/-- The points in the source lying over one field-valued test form a finite set. -/
theorem finite_sourceProjection_range (hπ : IsFinite π)
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : (schemeYoneda S).obj (Over.mk s) ⟶ F) :
    (Set.range (sourceProjection hπ a).left).Finite := by
  let : _root_.AlgebraicGeometry.IsFinite (testProjection hπ a).left :=
    testProjection_isFinite hπ a
  have ht : (Set.univ : Set (Over.mk s).left).Finite := by
    change (Set.univ : Set (Spec (CommRingCat.of K))).Finite
    exact Set.finite_univ
  have hw : (Set.univ : Set (sourceOverTest hπ a).left).Finite := by
    simpa only [Set.preimage_univ] using (testProjection hπ a).left.finite_preimage ht
  simpa only [Set.image_univ] using hw.image (sourceProjection hπ a).left

/-- Containing the complete represented fibre forces a test into the universal image. -/
theorem mem_universalImage_of_range_subset
    {V W : Over S} (a : (schemeYoneda S).obj T ⟶ F)
    (r : W ⟶ U) (p : W ⟶ T)
    (sq : IsPullback ((schemeYoneda S).map r) ((schemeYoneda S).map p) π a)
    (j : V ⟶ U) [_root_.AlgebraicGeometry.IsOpenImmersion j.left]
    (h : Set.range r.left ⊆ Set.range j.left) :
    uliftYonedaEquiv a ∈
      (universalImage π (Subfunctor.range ((schemeYoneda S).map j))).obj (op T) := by
  obtain ⟨b, hb⟩ := (factors_through_open_iff j r).mpr h
  have hrange : Subfunctor.range ((schemeYoneda S).map r) ≤
      Subfunctor.range ((schemeYoneda S).map j) := by
    rintro D x ⟨⟨d⟩, rfl⟩
    refine ⟨ULift.up (d ≫ b), ?_⟩
    change ULift.up ((d ≫ b) ≫ j) = ULift.up (d ≫ r)
    rw [Category.assoc, hb]
  have hle : Subfunctor.range a ≤
      universalImage π (Subfunctor.range ((schemeYoneda S).map j)) := by
    apply (universalImage_le_iff π _ _).mpr
    rw [← range_eq_preimage_of_isPullback sq.flip]
    exact hrange
  exact hle _ ⟨ULift.up (𝟙 T), rfl⟩

/-- An affine source open with its original map to the base scheme. -/
def affineOpenTest (V : U.left.affineOpens) : Over S :=
  Over.mk (V.val.ι ≫ U.hom)

/-- The inclusion of the affine source open. -/
def affineOpenInclusion (V : U.left.affineOpens) : affineOpenTest V ⟶ U :=
  Over.homMk V.val.ι

instance affineOpenInclusion_isOpenImmersion (V : U.left.affineOpens) :
    _root_.AlgebraicGeometry.IsOpenImmersion (affineOpenInclusion V).left :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion V.val.ι)

/-- The largest target subfunctor whose inverse image lies in an affine source open. -/
def universalAffineOpen (π : (schemeYoneda S).obj U ⟶ F)
    (V : U.left.affineOpens) : Subfunctor F :=
  universalImage π (Subfunctor.range ((schemeYoneda S).map (affineOpenInclusion V)))

theorem universalAffineOpen_isOpenImmersion (hπ : IsFinite π)
    (V : U.left.affineOpens) :
    IsOpenImmersion (universalAffineOpen π V).ι :=
  OpenSubfunctorDescent.universalImage_open_of_finite π hπ _
    (range_open _ (AffineOpenSubfunctors.isOpenImmersion_schemeYoneda_map _
      inferInstance))

/-- With an AF source, every field-valued test belongs to one of the universal opens. -/
theorem exists_universalAffineOpen_of_field_test (hπ : IsFinite π)
    (hU : PointTopology.HasFiniteAffineNeighborhoods U.left)
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : (schemeYoneda S).obj (Over.mk s) ⟶ F) :
    ∃ V : U.left.affineOpens,
      uliftYonedaEquiv a ∈ (universalAffineOpen π V).obj (op (Over.mk s)) := by
  obtain ⟨V, hV⟩ := hU _ (finite_sourceProjection_range hπ K s a)
  refine ⟨V, mem_universalImage_of_range_subset a
    (sourceProjection hπ a) (testProjection hπ a) (sourceOverTest_square hπ a)
    (affineOpenInclusion V) ?_⟩
  change Set.range (sourceProjection hπ a).left ⊆ Set.range V.val.ι
  rw [Scheme.Opens.range_ι]
  exact hV

end Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineUniversalNeighborhoods
