import Langlands.Geometry.Analytic.SchemeAnalytificationQuasiFiniteProperness
import Langlands.Geometry.Analytic.SpaceAnalytificationSchemeComparison
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullbacks
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedFunctorialityProof
import Langlands.Geometry.Analytic.AnalyticClosedImmersionTopology
import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability

/-! # Comparison and closed reflection for scheme maps into an affine spectrum -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.AlgebraicGeometry _root_.CategoryTheory Topology SaturatedAtlasPresentation
open Langlands.AlgebraicGeometry.AlgebraicSpace Langlands.AlgebraicGeometry.PointTopology
open AffineSchemeAnalytification SchemeAnalytification
open SchemeAnalytification.MorphismExistence

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type u} [CommRing A] [Algebra K A]

private abbrev specTopChart (A : Type u) [CommRing A] : (Spec (CommRingCat.of A)).affineOpens :=
  ⟨⊤, isAffineOpen_top _⟩

local instance specTopChart_isAffine (A : Type u) [CommRing A] :
    IsAffine (specTopChart A : Scheme.{u}) :=
  (specTopChart A).property

local instance specAlgebraMap_locallyOfFiniteType (K A : Type u) [CommRing K] [CommRing A]
    [Algebra K A] [Algebra.FiniteType K A] : LocallyOfFiniteType (Spec.algebraMap K A) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

private def specTopCoordinateMap (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] :
    A →ₐ[K] CoordinateRing (structureMap (Spec.algebraMap K A) (specTopChart A)) :=
  affineRingPointEquiv K A _ (schemeRingPointsEquiv K (ringTest K A) _
    (chartRingPoint K (Spec.algebraMap K A) (specTopChart A)))

private theorem spec_map_specTopCoordinateMap (K A : Type u) [CommRing K] [CommRing A]
    [Algebra K A] :
    Spec.map (CommRingCat.ofHom (specTopCoordinateMap K A).toRingHom) =
      (coordinateIso (structureMap (Spec.algebraMap K A) (specTopChart A))).inv ≫
        (Spec (CommRingCat.of A)).topIso.hom := by
  exact congrArg (fun t : _ ⟶ ringTest K A => t.left)
    (ringTestMap_affineRingPointEquiv K (schemeRingPointsEquiv K (ringTest K A) _
      (chartRingPoint K (Spec.algebraMap K A) (specTopChart A))))

private def specTopCoordinateEquiv (K A : Type u) [CommRing K] [CommRing A] [Algebra K A] :
    A ≃ₐ[K] CoordinateRing (structureMap (Spec.algebraMap K A) (specTopChart A)) := by
  let φ := CommRingCat.ofHom (specTopCoordinateMap K A).toRingHom
  have : IsIso (Scheme.Spec.map φ.op) := by
    change IsIso (Spec.map φ)
    rw [show Spec.map φ = _ from spec_map_specTopCoordinateMap K A]
    infer_instance
  have : IsIso φ.op := isIso_of_reflects_iso φ.op Scheme.Spec
  have : IsIso φ := inferInstanceAs (IsIso φ.op.unop)
  exact AlgEquiv.ofBijective (specTopCoordinateMap K A) (ConcreteCategory.bijective_of_isIso φ)

section Comparison

variable [Algebra.FiniteType K A] (P : FinitePolynomialPresentation K A)

set_option backward.isDefEq.respectTransparency false in
/-- The glued scheme analytification of `Spec A` and its supplied polynomial-locus
model are homeomorphic via the top chart coordinates. -/
def specSchemeComparisonHomeomorph :
    Space K (Spec.algebraMap K A) ≃ₜ AffineAnalytification.Space K P := by
  let Q := chartPresentation K (Spec.algebraMap K A) (specTopChart A)
  let ψ := AffineAnalytification.localizedHom K P Q (specTopCoordinateEquiv K A).toAlgHom
  let : IsIso ψ := isIso_localizedHom_of_algEquiv
    AffineAnalytification.affineAnalytificationLocalizedFunctoriality P Q (specTopCoordinateEquiv K A)
  exact (affineTopChartHomeomorph K (Spec.algebraMap K A)).symm.trans
    (TopCat.homeoOfIso (localizedSpaceFunctor.mapIso (asIso ψ)))

set_option backward.isDefEq.respectTransparency false in
private theorem specSchemeComparisonHomeomorph_ι
    (y : LocalSpace K (Spec.algebraMap K A) (specTopChart A)) :
    specSchemeComparisonHomeomorph P (ι K (Spec.algebraMap K A) (specTopChart A) y) =
      AffineAnalytification.baseMap K P (chartPresentation K (Spec.algebraMap K A)
        (specTopChart A)) (specTopCoordinateMap K A) y := by
  let e := affineTopChartHomeomorph K (Spec.algebraMap K A)
  let ψ := AffineAnalytification.localizedHom K P
    (chartPresentation K (Spec.algebraMap K A) (specTopChart A)) (specTopCoordinateMap K A)
  change (localizedSpaceFunctor.map ψ).hom (e.symm (e y)) = _
  rw [Homeomorph.symm_apply_apply, AffineAnalytification.localizedSpaceFunctor_map_localizedHom]
  rfl

end Comparison

variable {W : Over (Spec (CommRingCat.of K))} (q : W ⟶ ringTest K A)

omit [IsUltrametricDist K] [CompleteSpace K] in
set_option backward.isDefEq.respectTransparency false in
private theorem affineRingPointEquiv_comp_chartRingPoint (U : W.left.affineOpens)
    (h : (U : W.left.Opens) ≤ q.left ⁻¹ᵁ (specTopChart A : (Spec (CommRingCat.of A)).Opens)) :
    affineRingPointEquiv K A _
      (schemeRingPointsEquiv K W _ (chartRingPoint K W.hom U) ≫ q) =
        (openCoordinateMap q.left (Over.w q) (U := U) (V := specTopChart A) h).comp
          (specTopCoordinateMap K A) := by
  let E := affineRingPointEquiv K A (CoordinateRing (structureMap W.hom U))
  have hInv (φ : A →ₐ[K] CoordinateRing (structureMap W.hom U)) :
      E.symm φ = ringTestMap K φ := by
    have hφ := ringTestMap_affineRingPointEquiv K (E.symm φ)
    change ringTestMap K (E (E.symm φ)) = E.symm φ at hφ
    simpa only [Equiv.apply_symm_apply] using hφ.symm
  change E _ = _
  apply E.symm.injective
  rw [Equiv.symm_apply_apply, hInv, ringTestMap_comp]
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left, ringTestMap_left, ringTestMap_left,
    spec_map_specTopCoordinateMap]
  change ((U : W.left.Opens).toScheme.isoSpec.inv ≫ (U : W.left.Opens).ι) ≫ q.left =
    Spec.map (q.left.resLE _ _ h).appTop ≫
      ((specTopChart A : (Spec (CommRingCat.of A)).Opens).toScheme.isoSpec.inv ≫
        (Spec (CommRingCat.of A)).topIso.hom)
  rw [Category.assoc, Scheme.isoSpec_inv_naturality_assoc]
  exact (congrArg (fun m : (U : W.left.Opens).toScheme ⟶ (ringTest K A).left =>
    (U : W.left.Opens).toScheme.isoSpec.inv ≫ m)
    (Scheme.Hom.resLE_comp_ι q.left h)).symm

section Properness

variable [LocallyOfFiniteType W.hom] [_root_.AlgebraicGeometry.IsSeparated W.hom]
  [Algebra.FiniteType K A] (P : FinitePolynomialPresentation K A)
  {V : LocalizedCategory.{u, u, u} (K := K)} {v : PointFamily K ((schemeToSpace _).obj W) V}
  (hv : IsAnalytification K ((schemeToSpace _).obj W) V v)
  (s : V ⟶ AffineAnalytification.localized K P)
  (hs : ∀ (B : Type u) [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
    (z : RingPoints K ((schemeToSpace _).obj W) B),
      v B Q z ≫ s = AffineAnalytification.localizedHom K P Q
        (affineRingPointEquiv K A B (schemeRingPointsEquiv K W B z ≫ q)))

include hv hs in
set_option backward.isDefEq.respectTransparency false in
/-- A compatible morphism into the canonical affine model agrees on points
with the glued scheme analytification. -/
theorem specSchemeComparison_naturality (x : Space K W.hom) :
    specSchemeComparisonHomeomorph P
      (analytification K W.hom (Spec.algebraMap K A) q.left (Over.w q) x) =
        (localizedSpaceFunctor.map s).hom (schemeComparisonHomeomorph K W.hom v hv x) := by
  obtain ⟨U, y, rfl⟩ := exists_ι K W.hom x
  let T := specTopChart A
  let Q := chartPresentation K W.hom U
  let R := chartPresentation K (Spec.algebraMap K A) T
  have h : (U : W.left.Opens) ≤ q.left ⁻¹ᵁ (T : (Spec (CommRingCat.of A)).Opens) := by
    change (U : W.left.Opens) ≤ q.left ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)
    simp
  have hAn := isAnalytificationMap_analytification K W.hom (Spec.algebraMap K A) q.left (Over.w q)
  rw [hAn U T h, specSchemeComparisonHomeomorph_ι]
  change AffineAnalytification.baseMap K P R (specTopCoordinateMap K A)
      (AffineAnalytification.baseMap K R Q (openCoordinateMap q.left (Over.w q) h) y) =
    (localizedSpaceFunctor.map s).hom (chartComparison K W.hom v U y)
  let φ := affineRingPointEquiv K A _
    (schemeRingPointsEquiv K W _ (chartRingPoint K W.hom U) ≫ q)
  have hφ : φ = (openCoordinateMap q.left (Over.w q) h).comp (specTopCoordinateMap K A) :=
    affineRingPointEquiv_comp_chartRingPoint q U h
  rw [AffineAnalytification.MorphismComparison.baseMap_baseMap K P R Q _ _ φ
    (fun a => (congrArg (fun ψ : A →ₐ[K] _ => ψ a) hφ).symm) y]
  have heq := congrArg (fun m : AffineAnalytification.localized K Q ⟶
    AffineAnalytification.localized K P => (localizedSpaceFunctor.map m).hom y)
    (hs _ Q (chartRingPoint K W.hom U))
  rw [Functor.map_comp, AffineAnalytification.localizedSpaceFunctor_map_localizedHom] at heq
  exact heq.symm

include hv hs in
set_option backward.isDefEq.respectTransparency false in
/-- A quasi-compact algebraic monomorphism into `Spec A` is a closed immersion
if its compatible analytic morphism is a closed immersion. -/
theorem isClosedImmersion_of_closedImmersion_affine_scheme
    [QuasiCompact q.left] [Mono q.left] (hc : closedImmersion s) :
    _root_.AlgebraicGeometry.IsClosedImmersion q.left := by
  let e := schemeComparisonHomeomorph K W.hom v hv
  let d := specSchemeComparisonHomeomorph P
  let F := analytification K W.hom (Spec.algebraMap K A) q.left (Over.w q)
  have hF : (F : Space K W.hom → Space K (Spec.algebraMap K A)) =
      d.symm ∘ (localizedSpaceFunctor.map s).hom ∘ e := by
    funext x
    change F x = d.symm ((localizedSpaceFunctor.map s).hom (e x))
    rw [← specSchemeComparison_naturality q P hv s hs x]
    exact (d.symm_apply_apply (F x)).symm
  have hp : IsProperMap F := by
    rw [hF]
    exact d.symm.isProperMap.comp (hc.isClosedEmbedding.isProperMap.comp e.isProperMap)
  have : LocallyOfFiniteType (q.left ≫ (ringTest K A).hom) := by
    rw [Over.w q]
    infer_instance
  have : _root_.AlgebraicGeometry.IsSeparated (q.left ≫ (ringTest K A).hom) := by
    rw [Over.w q]
    infer_instance
  have : LocallyOfFiniteType q.left := locallyOfFiniteType_of_comp q.left (ringTest K A).hom
  have : _root_.AlgebraicGeometry.IsSeparated q.left :=
    _root_.AlgebraicGeometry.IsSeparated.of_comp q.left (ringTest K A).hom
  have : IsFinite q.left :=
    isFinite_of_isProperMap_analytification K W.hom (Spec.algebraMap K A) q.left (Over.w q) hp
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mpr
    ⟨inferInstance, inferInstance⟩

end Properness

end Langlands.Analytic.SpaceAnalytification
