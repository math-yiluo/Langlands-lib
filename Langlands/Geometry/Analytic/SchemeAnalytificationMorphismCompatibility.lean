import Langlands.Geometry.Analytic.SchemeAnalytificationMorphismStatement
import Langlands.Geometry.Analytic.AnalytificationCenterStatement
import Langlands.Geometry.Analytic.AnalytificationCenterComparison

/-! # Center and rational-point compatibility for scheme analytification maps -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.MorphismCompatibility

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Analytic.AffineSchemeAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  (f' : Y ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFiniteType f']

/-- The center of a local image is the image under the original scheme morphism. -/
theorem localCenter_morphismLocalMap (g : X ⟶ Y) (hg : g ≫ f' = f)
    {U : X.affineOpens} {V : Y.affineOpens}
    (h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens)) (y : LocalSpace K f U) :
    localCenter K f' V (morphismLocalMap K f f' g hg h y) =
      g (localCenter K f U y) := by
  have hpoint : localCenterPoint K f' V (morphismLocalMap K f f' g hg h y) =
      Spec.map (g.resLE (V : Y.Opens) (U : X.Opens) h).appTop
        (localCenterPoint K f U y) :=
    AffineAnalytification.center_baseMap K _ _ (openCoordinateMap g hg h) y
  rw [localCenter_apply, localCenter_apply, hpoint, affineOpenMap, affineOpenMap,
    ← Scheme.Hom.comp_apply, Scheme.isoSpec_inv_naturality_assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  rfl

/-- If the center preimages are the chart images, charts subordinate to any scheme
morphism cover the glued analytification. -/
theorem exists_subordinate_chart
    (hRange : ∀ U : X.affineOpens,
      center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U))
    (g : X ⟶ Y) (z : Space K f) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens)
      (_h : (U : X.Opens) ≤ g ⁻¹ᵁ (V : Y.Opens))
      (y : LocalSpace K f U), ι K f U y = z := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g (center K f z))) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show center K f z ∈ g ⁻¹ᵁ V from hxV) (g ⁻¹ᵁ V).isOpen
  have hz : z ∈ Set.range (ι K f ⟨U, hU⟩) := by
    rw [← hRange]
    exact hxU
  obtain ⟨y, hy⟩ := hz
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hUV, y, hy⟩

/-- Every analytification map commutes with centers, once center preimages of
source affine opens are identified with chart images. -/
theorem center_map
    (hRange : ∀ U : X.affineOpens,
      center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U))
    (g : X ⟶ Y) (hg : g ≫ f' = f)
    (F : C(Space K f, Space K f')) (hF : IsAnalytificationMap K f f' g hg F)
    (z : Space K f) : center K f' (F z) = g (center K f z) := by
  obtain ⟨U, V, h, y, rfl⟩ := exists_subordinate_chart K f hRange g z
  rw [hF U V h y, center_ι, center_ι]
  exact localCenter_morphismLocalMap K f f' g hg h y

/-- Center naturality and singleton fibers over rational centers imply
rational-point naturality, independently of center surjectivity. -/
theorem rationalPoint_map
    (g : X ⟶ Y) (hg : g ≫ f' = f) (F : Space K f → Space K f')
    (hmap : ∀ z : Space K f, center K f' (F z) = g (center K f z))
    (hSource : ∀ p : RingPoint K (Over.mk f) K,
      center K f (analyticRationalPoint K f p) = p.left (IsLocalRing.closedPoint K))
    (hTarget : ∀ p : RingPoint K (Over.mk f') K,
      center K f' (analyticRationalPoint K f' p) = p.left (IsLocalRing.closedPoint K))
    (hFiber : ∀ (p : RingPoint K (Over.mk f') K) (z : Space K f'),
      center K f' z = center K f' (analyticRationalPoint K f' p) →
        z = analyticRationalPoint K f' p)
    (p : RingPoint K (Over.mk f) K) :
    F (analyticRationalPoint K f p) =
      analyticRationalPoint K f' (p ≫ Over.homMk g hg) := by
  apply hFiber (p ≫ Over.homMk g hg)
  exact (hmap _).trans
    ((congrArg (fun x : X => g x) (hSource p)).trans
      (hTarget (p ≫ Over.homMk g hg)).symm)

/-- The two compatibility clauses need only the chart preimage-range formulas
and injectivity of seminorms on target charts. -/
theorem compatibility_of_range_and_seminorm_injective
    (hRange : ∀ U : X.affineOpens,
      center K f ⁻¹' ((U : X.Opens) : Set X) = Set.range (ι K f U))
    (hRange' : ∀ V : Y.affineOpens,
      center K f' ⁻¹' ((V : Y.Opens) : Set Y) = Set.range (ι K f' V))
    (hInjective : ∀ V : Y.affineOpens,
      Function.Injective (AffineAnalytification.pointSeminorm K (chartPresentation K f' V)))
    (g : X ⟶ Y) (hg : g ≫ f' = f)
    (F : C(Space K f, Space K f')) (hF : IsAnalytificationMap K f f' g hg F) :
    (∀ z : Space K f, center K f' (F z) = g (center K f z)) ∧
      ∀ p : RingPoint K (Over.mk f) K,
        F (analyticRationalPoint K f p) =
          analyticRationalPoint K f' (p ≫ Over.homMk g hg) := by
  have hmap := center_map K f f' hRange g hg F hF
  exact ⟨hmap, rationalPoint_map K f f' g hg F hmap
    (CenterComparison.center_analyticRationalPoint K f)
    (CenterComparison.center_analyticRationalPoint K f')
    (CenterComparison.eq_analyticRationalPoint_of_center_eq K f' hRange' hInjective)⟩

/-- Compatibility of any analytification map with centers and rational points
follows from the scheme part of the center theorem. -/
theorem compatibility_of_center (hCenter : AnalytificationCenterStatement.{u, u})
    (g : X ⟶ Y) (hg : g ≫ f' = f)
    (F : C(Space K f, Space K f')) (hF : IsAnalytificationMap K f f' g hg F) :
    (∀ z : Space K f, center K f' (F z) = g (center K f z)) ∧
      ∀ p : RingPoint K (Over.mk f) K,
        F (analyticRationalPoint K f p) =
          analyticRationalPoint K f' (p ≫ Over.homMk g hg) := by
  have hmap := center_map K f f' (hCenter.2 K X f).2.1 g hg F hF
  exact ⟨hmap, rationalPoint_map K f f' g hg F hmap
    (hCenter.2 K X f).2.2.1 (hCenter.2 K Y f').2.2.1 (hCenter.2 K Y f').2.2.2⟩

end Langlands.Analytic.SchemeAnalytification.MorphismCompatibility
