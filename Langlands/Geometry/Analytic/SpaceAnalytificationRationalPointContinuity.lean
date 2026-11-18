import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointNaturalityProof
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartOpenMap
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily

/-! # Continuity of the rational-point map of an algebraic-space analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory Opposite Topology SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an affine test point to a ground-field algebra point computes
the same analytic point by the affine chart map. -/
theorem IsAnalytification.rationalPoint_changeRing (hp : IsAnalytification K X Y p)
    (P₀ : FinitePolynomialPresentation K K)
    {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (x : RingPoints K X A) (φ : AlgPoint K A K) :
    rationalPoint p P₀ (RingPoints.changeRing φ.toAlgHom x) =
      localizedSpaceFunctor.map (p A P x) (AffineAnalytification.analyticPoint K P φ) := by
  unfold rationalPoint
  rw [hp.naturality P P₀ φ.toAlgHom x, Functor.map_comp, TopCat.comp_app,
    AffineAnalytification.localizedSpaceFunctor_map_localizedHom]
  change localizedSpaceFunctor.map (p A P x)
    (AffineAnalytification.baseMap K P P₀ φ.toAlgHom
      (AffineAnalytification.analyticPoint K P₀ (AlgPoint.ofAlgHom (AlgHom.id K K)))) = _
  rw [AffineAnalytification.affineAnalytificationRationalPointNaturality K A K P P₀]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- The rational-point map is continuous after any locally finite-type affine
scheme map to the algebraic space. -/
theorem IsAnalytification.continuous_affine_schemePointsMap
    (hp : IsAnalytification K X Y p) (P₀ : FinitePolynomialPresentation K K)
    {U : Over (Spec (CommRingCat.of K))} [IsAffine U.left] [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) :
    Continuous (rationalPoint p P₀ ∘ schemePointsMap a) := by
  let C := AffineCoordinateRing K U
  let P := FinitePolynomialPresentation.ofFiniteType K C
  let e := affineSchemeOverIso K U
  let aC := (schemeYoneda _).map e.inv ≫ a
  let xC : RingPoints K X C := uliftYonedaEquiv aC
  have heq (q : RingPoint K U K) :
      RingPoints.changeRing (affineSchemePointEquiv K U K q).toAlgHom xC =
        schemePointsMap a q := by
    let φ := affineSchemePointEquiv K U K q
    have hq : ringTestMap K φ.toAlgHom = q ≫ e.hom := by
      apply Over.OverMorphism.ext
      exact affineSchemePointEquiv_spec K K q
    change X.presheaf.map (ringTestMap K φ.toAlgHom).op (uliftYonedaEquiv aC) = _
    rw [← schemeYoneda_app_up aC (ringTestMap K φ.toAlgHom)]
    change a.app (op (ringTest K K)) (ULift.up (ringTestMap K φ.toAlgHom ≫ e.inv)) = _
    rw [hq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have he : (rationalPoint p P₀ ∘ schemePointsMap a) =
      (fun q : RingPoint K U K => localizedSpaceFunctor.map (p C P xC)
        (AffineAnalytification.analyticPoint K P (affineSchemePointEquiv K U K q))) := by
    funext q
    rw [Function.comp_apply, ← heq q]
    exact hp.rationalPoint_changeRing P₀ P xC _
  rw [he]
  exact (localizedSpaceFunctor.map (p C P xC)).hom.continuous.comp
    (((AffineAnalytification.affineAnalytificationRationalPoints K C P).2.1).continuous.comp
      (affineSchemePointHomeomorph K U K).continuous)

set_option backward.isDefEq.respectTransparency false in
/-- The rational-point map is continuous after any locally finite-type scheme
map to the algebraic space, for the actual scheme point topology. -/
theorem IsAnalytification.continuous_schemePointsMap
    (hp : IsAnalytification K X Y p) (P₀ : FinitePolynomialPresentation K K)
    {U : Over (Spec (CommRingCat.of K))} [LocallyOfFiniteType U.hom]
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) :
    Continuous[schemePointTopology K U K, _] (rationalPoint p P₀ ∘ schemePointsMap a) := by
  rw [schemePointTopology, continuous_iSup_dom]
  intro V
  let : IsAffine (openOver K U V.val).left := V.property
  have : LocallyOfFiniteType (openOver K U V.val).hom := by
    change LocallyOfFiniteType (V.val.ι ≫ U.hom)
    infer_instance
  apply continuous_coinduced_dom.mpr
  have h := hp.continuous_affine_schemePointsMap P₀
    ((schemeYoneda _).map (openOverι K U V.val) ≫ a)
  exact h

/-- All presentation-dependent rational-point maps are continuous for the
étale-chart topology. -/
def RationalPointMapsContinuous : Prop :=
  ∀ P₀ : FinitePolynomialPresentation K K,
    Continuous[etaleChartTopology K X, _] (rationalPoint p P₀)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality and the published affine rational-point comparison imply
continuity for the étale-chart topology. -/
theorem IsAnalytification.continuous_rationalPoint (hp : IsAnalytification K X Y p)
    (P₀ : FinitePolynomialPresentation K K) :
    Continuous[etaleChartTopology K X, _] (rationalPoint p P₀) := by
  apply (etaleChartTopology_continuous_iff (rationalPoint p P₀)).mpr
  intro c
  let := c.locallyOfFiniteType
  rw [c.pointMap_eq]
  exact hp.continuous_schemePointsMap P₀ (AlgebraicSpace.hom c.hom)

end Langlands.Analytic.SpaceAnalytification
