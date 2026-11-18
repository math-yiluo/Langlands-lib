import Langlands.Geometry.Analytic.SpaceAnalytificationFieldPointReduction
import Langlands.Geometry.Analytic.SpaceAnalytificationRationalPointInjectivity
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullback
import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsProof
import Langlands.Geometry.Analytic.AffineAnalytificationExtensionCoordinateMaps
import Langlands.Geometry.Analytic.FiniteGaloisFieldPointLifts
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.Geometry.Analytic.LocalizedEtaleFieldPointPullbackProof
import Langlands.Geometry.Analytic.ValuedField.CompleteAlgebraicClosure
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteGaloisExtensionPointTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints

/-! # Base-field points of the analytification of an algebraic space -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open AffinoidAtlasPresentation SaturatedAtlasPresentation AffineAnalytification
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology (ringTestMap ringTestMap_comp AlgPoint)

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}

/-- Two extension-valued points on the same affine test have the same algebraic
image when their full analytic images coincide. -/
private theorem changeRing_eq_of_fieldPoint_image_eq
    (hX : IsSeparated X) (hp : IsAnalytification K X Y p)
    {A E : Type u} [CommRing A] [Algebra K A] [NormedField E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] [IsAlgClosed E]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X A)
    (hx : etale (p A P x))
    (q r : (localizedFieldPointFunctor E).obj (localized K P))
    (hqr : (localizedFieldPointFunctor E).map (p A P x) q =
      (localizedFieldPointFunctor E).map (p A P x) r) :
    RingPoints.changeRing (extensionAlgHom K P q) x =
      RingPoints.changeRing (extensionAlgHom K P r) x := by
  obtain ⟨C, _, _, R, f, g, -, hpb⟩ := hasClosedAffinePointPullbacks_of_isSeparated hX A P A P x x
  let fAn := localizedHom K P R f
  let gAn := localizedHom K P R g
  have hAn : IsPullback fAn gAn (p A P x) (p A P x) := hp.isPullback P P R f g x x hpb
  have hE := localizedEtaleFieldPointPullback (K := K) (L := E) fAn gAn (p A P x) (p A P x) hx hAn
  obtain ⟨t, ht₁, ht₂⟩ := Types.exists_of_isPullback hE q r hqr
  let ψ := extensionAlgHom K R t
  have hq : ψ.comp f = extensionAlgHom K P q := by
    rw [← extensionAlgHom_localizedHom K P R f t, ht₁]
  have hr : ψ.comp g = extensionAlgHom K P r := by
    rw [← extensionAlgHom_localizedHom K P R g t, ht₂]
  rw [← hq, ← hr]
  apply (uliftYonedaEquiv.{u + 1}).symm.injective
  have hw := congrArg (fun k => (schemeYoneda _).map (ringTestMap K ψ) ≫ k) hpb.w
  simp only [← Category.assoc, ← Functor.map_comp, ← ringTestMap_comp] at hw
  exact (uliftYonedaEquiv_symm_map (F := X.presheaf) (ringTestMap K (ψ.comp f)).op x).trans
    (hw.trans (uliftYonedaEquiv_symm_map (F := X.presheaf) (ringTestMap K (ψ.comp g)).op x).symm)

/-- The algebraic image of a full point above a full base-field point is fixed
by every base-field automorphism of its finite value field. -/
private theorem changeRing_fixed_of_fieldPoint_over_base
    (hX : IsSeparated X) (hp : IsAnalytification K X Y p)
    {A L : Type u} [CommRing A] [Algebra K A] [NormedField L] [NormedAlgebra K L]
    [IsUltrametricDist L] [FiniteDimensional K L]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X A) (hx : etale (p A P x))
    (q : (localizedFieldPointFunctor K).obj Y)
    (s : (localizedFieldPointFunctor L).obj (localized K P))
    (hs : localizedSpaceFunctor.map (p A P x)
      (((localizedFieldPointProjection L).app (localized K P) s).down) =
        ((localizedFieldPointProjection K).app Y q).down)
    (σ : L ≃ₐ[K] L) :
    RingPoints.changeRing σ.toAlgHom (RingPoints.changeRing (extensionAlgHom K P s) x) =
      RingPoints.changeRing (extensionAlgHom K P s) x := by
  let E := ValuedField.CompleteAlgebraicClosure K
  let i : L →ₐ[K] E := IsAlgClosed.lift
  let j := i.comp σ.toAlgHom
  have hi (a : L) : ‖i a‖ = ‖a‖ :=
    (isometry_algHom_of_isAlgebraic i).norm_map_of_map_zero (map_zero i) a
  have hj (a : L) : ‖j a‖ = ‖a‖ :=
    (isometry_algHom_of_isAlgebraic j).norm_map_of_map_zero (map_zero j) a
  let t : (localizedFieldPointFunctor E).obj (localized K P) := FieldPoint.mapValue s i hi
  let t' : (localizedFieldPointFunctor E).obj (localized K P) := FieldPoint.mapValue s j hj
  let F := localizedFieldPointFunctor (K := K) E
  have ht : F.map (p A P x) t = F.map (p A P x) t' := by
    apply localizedFieldPoint_eq_of_projection_eq_at_baseFieldPoint (K := K) (L := E) Y q
    · exact (localizedFieldPointProjection_down_naturality (p A P x) t).trans hs
    · exact (localizedFieldPointProjection_down_naturality (p A P x) t').trans hs
  have he := changeRing_eq_of_fieldPoint_image_eq hX hp P x hx t' t ht.symm
  have hφ : extensionAlgHom K P t = i.comp (extensionAlgHom K P s) :=
    extensionAlgHom_mapValue K P s i hi
  have hφ' : extensionAlgHom K P t' = j.comp (extensionAlgHom K P s) :=
    extensionAlgHom_mapValue K P s j hj
  rw [hφ', hφ] at he
  apply RelativeIntegralPoints.changeRing_injective hX i i.injective
  simpa only [RingPoints.changeRing_comp, AlgHom.comp_assoc, j] using he

/-- The projection of every full base-field point is in the image of the
algebraic rational-point map. -/
private theorem rationalPoint_image_of_fieldPoint
    (hX : IsSeparated X) (hp : IsAnalytification K X Y p)
    (P₀ : FinitePolynomialPresentation K K) (q : (localizedFieldPointFunctor K).obj Y) :
    ∃ x₀ : RingPoints K X K,
      rationalPoint p P₀ x₀ = ((localizedFieldPointProjection K).app Y q).down := by
  obtain ⟨A, _, _, P, x, hx, z, hz⟩ := hp.jointly_surjective
    (((localizedFieldPointProjection K).app Y q).down)
  have hEt := hp.etale_map P x hx
  obtain ⟨L, _, _, _, _, _, _, s, hs⟩ := exists_finiteGalois_fieldPoint_of_etale hEt q z hz
  let φ := extensionAlgHom K P s
  have hfix := changeRing_fixed_of_fieldPoint_over_base hX hp P x hEt q s
    ((congrArg (localizedSpaceFunctor.map (p A P x)) hs).trans hz)
  obtain ⟨x₀, hx₀⟩ := ExtensionClosedRange.exists_desc_of_finite_galois_fixed hX
    (RingPoints.changeRing φ x) hfix
  let Q := FinitePolynomialPresentation.ofFiniteType K L
  let ν : MulRingSeminorm L :=
    { normRingSeminorm L with map_one' := norm_one, map_mul' := norm_mul }
  have hn : ExtendsNorm K ν := norm_algebraMap' L
  obtain ⟨t, ht⟩ : ν ∈ Set.range (pointSeminorm K Q) := by
    rw [SeminormComparison.range_pointSeminorm]
    exact hn
  have htz : localizedSpaceFunctor.map (localizedHom K P Q φ) t = z := by
    rw [localizedSpaceFunctor_map_localizedHom]
    apply SeminormComparison.pointSeminorm_injective K P
    ext a
    change pointSeminorm K P (baseMap K P Q φ t) a = pointSeminorm K P z a
    rw [pointSeminorm_baseMap, ht]
    change ‖φ a‖ = pointSeminorm K P z a
    change s.point = z at hs
    rw [← hs]
    exact norm_extensionAlgHom K P s a
  have ht₀ : localizedSpaceFunctor.map (localizedHom K P₀ Q (Algebra.ofId K L)) t =
      analyticPoint K P₀ (AlgPoint.ofAlgHom (AlgHom.id K K)) := by
    rw [localizedSpaceFunctor_map_localizedHom]
    apply SeminormComparison.pointSeminorm_injective K P₀
    ext a
    change pointSeminorm K P₀ (baseMap K P₀ Q (Algebra.ofId K L) t) a = _
    rw [pointSeminorm_baseMap, ht, RationalPointComparison.pointSeminorm_analyticPoint_apply]
    exact norm_algebraMap' L a
  change ↑(localizedSpaceFunctor.obj (localized K Q)) at t
  refine ⟨x₀, ?_⟩
  have hscalar : localizedSpaceFunctor.map (p L Q (RingPoints.changeRing (Algebra.ofId K L) x₀)) t =
      rationalPoint p P₀ x₀ := by
    rw [hp.naturality P₀ Q (Algebra.ofId K L) x₀, Functor.map_comp, TopCat.comp_app, ht₀]
    rfl
  rw [hx₀] at hscalar
  have hchart : localizedSpaceFunctor.map (p L Q (RingPoints.changeRing φ x)) t =
      localizedSpaceFunctor.map (p A P x) z := by
    rw [hp.naturality P Q φ x, Functor.map_comp, TopCat.comp_app, htz]
  exact hscalar.symm.trans (hchart.trans hz)

/-- Algebraic `K`-points are precisely the full `K`-valued points of a
separated algebraic space's analytification, with the specified projection. -/
theorem spaceAnalytificationFieldPoints : SpaceAnalytificationFieldPointsStatement.{u} := by
  intro K _ _ _ X hX _ Y p hp
  refine ⟨localizedFieldPointProjection_injective Y, fun P₀ => ?_⟩
  exact fieldPointEquiv_of_rationalPoint_image affineAnalytificationRationalPoints p P₀
    (rationalPoint_injective_of_pointLifting (fun _ _ _ _ h => hasPointLifting_of_isPullback h)
      hX hp P₀)
    (rationalPoint_image_of_fieldPoint hX hp P₀)

end Langlands.Analytic.SpaceAnalytification
