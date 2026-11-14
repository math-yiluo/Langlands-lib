import Langlands.Geometry.Building.ValuationApartmentMetric
import Langlands.Geometry.Building.RootApartmentFieldDescent
import Langlands.Geometry.Building.IntegerValuationLocalComparison

/-! # Canonical root metrics under actual field comparison maps -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace RootTranslationMetric

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance extendedAffine : IsAffineHom (CategoryTheory.Functor.obj (GroupScheme.baseChange b) G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Fintype (relativeRoots i)]

attribute [local instance] normedAddCommGroup normedSpace

local instance [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] : NormedAddCommGroup (TranslationSpace (S := S_K) i_K) :=
  normedAddCommGroup (F := K) (S := S_K) (G := baseChanged k K G) i_K

local instance [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] : NormedSpace ℝ (TranslationSpace (S := S_K) i_K) :=
  normedSpace (F := K) (S := S_K) (G := baseChanged k K G) i_K

/-- Actual split-torus base change preserves the canonical root norm, including
for field isomorphisms. The valuation is not rescaled. -/
theorem norm_splitTranslationBaseChange
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] (v : TranslationSpace i) :
    ‖splitTranslationBaseChange (K := K) hS i v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq (S := S_K) (G := baseChanged k K G) i_K, norm_sq i]
  let e : relativeRoots i ≃ relativeRoots (T := S_K) i_K :=
    rootsBaseChangeEquiv (K := K) G S hS i
  exact (Fintype.sum_equiv e _ _
    (fun a => congrArg (fun r : ℝ => r ^ 2)
      (rootForm_splitTranslationBaseChange (K := K) hS i a v).symm)).symm

/-- Inverse actual base change preserves the same canonical norms. -/
theorem norm_splitTranslationBaseChange_symm
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (v : TranslationSpace (S := S_K) i_K) :
    ‖(splitTranslationBaseChange (K := K) hS i).symm v‖ = ‖v‖ := by
  obtain ⟨w, rfl⟩ := (splitTranslationBaseChange (K := K) hS i).surjective v
  rw [LinearEquiv.symm_apply_apply, norm_splitTranslationBaseChange]

/-- The existing reduced translation equivalence, with its root-norm isometry. -/
def splitTranslationBaseChangeLinearIsometryEquiv
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] :
    TranslationSpace i ≃ₗᵢ[ℝ] TranslationSpace (S := S_K) i_K where
  toLinearEquiv := splitTranslationBaseChange (K := K) hS i
  norm_map' := norm_splitTranslationBaseChange hS i

@[simp] theorem splitTranslationBaseChangeLinearIsometryEquiv_apply
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (v : TranslationSpace i) :
    splitTranslationBaseChangeLinearIsometryEquiv (K := K) hS i v =
      splitTranslationBaseChange (K := K) hS i v := rfl

end RootTranslationMetric

namespace KPApartmentData

section FieldRestriction

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance restrictedExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom b)
  infer_instance

private instance restrictedExtendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

variable [Fintype (relativeRoots i)]
  (hS : IsSplitTorus S.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs i)
  (ω : Kˣ →* Multiplicative ℝ)
  (hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0)

attribute [local instance] RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace

local instance [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] : NormedAddCommGroup (TranslationSpace (S := S_K) i_K) :=
  RootTranslationMetric.normedAddCommGroup (F := K) (S := S_K) (G := baseChanged k K G) i_K

local instance [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)] : NormedSpace ℝ (TranslationSpace (S := S_K) i_K) :=
  RootTranslationMetric.normedSpace (F := K) (S := S_K) (G := baseChanged k K G) i_K

omit [Fintype (relativeRoots i)] in
/-- Each original root reads the restricted displacement as its actual
base-changed root reads the original upstairs displacement. -/
theorem rootForm_vsub_fieldRestrictAffineEquiv
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    (a : relativeRoots i) (x y : D.Apartment) :
    rootForm i a (fieldRestrictAffineEquiv i hS hE ω hω D x -ᵥ
      fieldRestrictAffineEquiv i hS hE ω hω D y) =
      rootForm (S := S_K) i_K (rootsBaseChangeEquiv (K := K) G S hS i a)
        (x -ᵥ y) := by
  change rootForm i a
    ((fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap x -ᵥ
      (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap y) = _
  rw [← (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap.linearMap_vsub]
  change rootForm i a ((splitTranslationBaseChange (K := K) hS i).symm (x -ᵥ y)) = _
  simpa only [LinearEquiv.apply_symm_apply] using
    (rootForm_splitTranslationBaseChange (K := K) hS i a
      ((splitTranslationBaseChange (K := K) hS i).symm (x -ᵥ y))).symm

/-- Literal field restriction preserves the root norm of the original affine
displacements. Its linear part is inverse actual reduced base change. -/
theorem norm_vsub_fieldRestrictAffineEquiv
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd)) (x y : D.Apartment) :
    ‖fieldRestrictAffineEquiv i hS hE ω hω D x -ᵥ
      fieldRestrictAffineEquiv i hS hE ω hω D y‖ =
      ‖(x -ᵥ y : TranslationSpace (S := S_K) i_K)‖ := by
  change ‖(fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap x -ᵥ
    (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap y‖ = _
  rw [← (fieldRestrictAffineEquiv i hS hE ω hω D).toAffineMap.linearMap_vsub]
  change ‖(splitTranslationBaseChange (K := K) hS i).symm (x -ᵥ y)‖ = _
  exact RootTranslationMetric.norm_splitTranslationBaseChange_symm hS i _

/-- The actual affine field restriction is isometric for metrics realizing the
canonical root norms on the original affine spaces. -/
theorem isometry_fieldRestrictAffineEquiv
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    [MetricSpace D.Apartment]
    [MetricSpace (fieldRestrict i hS hE ω hω D).Apartment]
    (hD : ∀ x y : D.Apartment, dist x y =
      ‖(x -ᵥ y : TranslationSpace (S := S_K) i_K)‖)
    (hR : ∀ x y : (fieldRestrict i hS hE ω hω D).Apartment,
      dist x y = ‖(x -ᵥ y : TranslationSpace i)‖) :
    Isometry (fieldRestrictAffineEquiv i hS hE ω hω D) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [hR, hD]
  exact norm_vsub_fieldRestrictAffineEquiv i hS hE ω hω D x y

/-- The existing literal apartment restriction, bundled as an isometric
equivalence for the canonical root metrics. -/
def fieldRestrictIsometryEquiv
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    [MetricSpace D.Apartment]
    [MetricSpace (fieldRestrict i hS hE ω hω D).Apartment]
    (hD : ∀ x y : D.Apartment, dist x y =
      ‖(x -ᵥ y : TranslationSpace (S := S_K) i_K)‖)
    (hR : ∀ x y : (fieldRestrict i hS hE ω hω D).Apartment,
      dist x y = ‖(x -ᵥ y : TranslationSpace i)‖) :
    D.Apartment ≃ᵢ (fieldRestrict i hS hE ω hω D).Apartment where
  toEquiv := (fieldRestrictAffineEquiv i hS hE ω hω D).toEquiv
  isometry_toFun := isometry_fieldRestrictAffineEquiv i hS hE ω hω D hD hR

@[simp] theorem fieldRestrictIsometryEquiv_apply
    [Fintype (relativeRoots (k := K) (T := S_K) (G := baseChanged k K G) i_K)]
    (D : KPApartmentData (S := S_K) (G := G_K) i_K (fun t => (ω t).toAdd))
    [MetricSpace D.Apartment]
    [MetricSpace (fieldRestrict i hS hE ω hω D).Apartment]
    (hD : ∀ x y : D.Apartment, dist x y =
      ‖(x -ᵥ y : TranslationSpace (S := S_K) i_K)‖)
    (hR : ∀ x y : (fieldRestrict i hS hE ω hω D).Apartment,
      dist x y = ‖(x -ᵥ y : TranslationSpace i)‖)
    (x : D.Apartment) :
    fieldRestrictIsometryEquiv i hS hE ω hω D hD hR x =
      fieldRestrictPoint i hS hE ω hω D x := rfl

end FieldRestriction

section ReindexOrder

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ω ω' : kˣ → ℝ} (D : KPApartmentData i ω) (h : ω = ω')

/-- Reindexing along an equality of field orders leaves the original affine
displacements unchanged. -/
theorem vsub_reindexOrderApartment (x y : D.Apartment) :
    D.reindexOrderApartment h x -ᵥ D.reindexOrderApartment h y =
      (x -ᵥ y : TranslationSpace i) := by
  cases h
  rfl

variable [Fintype (relativeRoots i)]

attribute [local instance] RootTranslationMetric.normedAddCommGroup
  RootTranslationMetric.normedSpace

/-- Equality transport of the field order is isometric for any two metrics
realizing the canonical root norm on the original affine differences. -/
theorem isometry_reindexOrderApartment
    [MetricSpace D.Apartment] [MetricSpace (D.reindexOrder h).Apartment]
    (hD : ∀ x y : D.Apartment, dist x y = ‖(x -ᵥ y : TranslationSpace i)‖)
    (hR : ∀ x y : (D.reindexOrder h).Apartment,
      dist x y = ‖(x -ᵥ y : TranslationSpace i)‖) :
    Isometry (D.reindexOrderApartment h) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [hR, hD, vsub_reindexOrderApartment]

end ReindexOrder

end KPApartmentData

end Langlands.Geometry.Building
