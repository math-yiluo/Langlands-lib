import Langlands.GroupScheme.Torus.TransporterFunctoriality
import Langlands.GroupScheme.Torus.ExponentHomomorphisms
import Langlands.GroupScheme.Torus.RelativeSelfCentralizingLocus
import Langlands.GroupScheme.RelativeIdentityComponent.SectionNeighbourhood

/-! # Relative transporter sections in actual geometric identity components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

variable {S : Scheme.{u}} (I : Type u) [Fintype I]
  (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]

local instance transporter_smooth_pullback {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) :
    Smooth ((baseChange q).obj G).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom q))

local instance transporter_affine_pullback {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) :
    IsAffineHom ((baseChange q).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom q))

/-- The actual standard-torus map into the actual identity component of a
specified field pullback, with its original torus coordinates. -/
def fieldIdentityTorusHom {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) (i : splitTorus S I ⟶ G) :
    splitTorus (Spec (CommRingCat.of K)) I ⟶ identityComponent ((baseChange q).obj G) :=
  IdentityComponent.torusHom (T := commGroupScheme _ I)
    ((baseChangeIso q I).inv ≫ (baseChange q).map i) (isSplitTorus_splitTorus I)

@[reassoc (attr := simp)]
theorem fieldIdentityTorusHom_comp {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) (i : splitTorus S I ⟶ G) :
    fieldIdentityTorusHom I G q i ≫ identityComponentι ((baseChange q).obj G) =
      (baseChangeIso q I).inv ≫ (baseChange q).map i :=
  IdentityComponent.torusHom_comp _ _

variable {g : S ⟶ G.X.left} {s : S}
  (d : RelativeIdentityComponent.SectionIdentityNeighbourhoodData G g s)
  (hg : g ≫ G.X.hom = 𝟙 S)
  (i₁ i₂ : splitTorus S I ⟶ G)
  (htrans : PointwiseSchemeAction.IsTransporter i₁ i₂
    (show Over.mk (𝟙 S) ⟶ G.X from Over.homMk g hg))

include htrans

omit [Smooth G.X.hom] [IsAffineHom G.X.hom] in
/-- The actual field section point is a transporter for the actual
base-changed maps, preserving the standard torus coordinates. -/
theorem fieldSection_isTransporter {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) :
    PointwiseSchemeAction.IsTransporter
      ((baseChangeIso q I).inv ≫ (baseChange q).map i₁)
      ((baseChangeIso q I).inv ≫ (baseChange q).map i₂)
      (d.fieldSection hg q) := by
  have hfield := htrans.baseChange q (V := 𝟙_ (Over (Spec (CommRingCat.of K))))
    (Over.homMk q (by simp)) (d.fieldSection hg q) (by
      unfold RelativeIdentityComponent.SectionIdentityNeighbourhoodData.fieldSection
      rw [MulEquiv.apply_symm_apply]
      apply Over.OverMorphism.ext
      rfl)
  exact hfield.precomp (baseChangeIso q I).inv

omit htrans in
/-- Actual identity-component transporter data, retaining inclusion recovery
to the original field section. -/
structure FieldIdentityTransporterData {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S) where
  point : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶
    (identityComponent ((baseChange q).obj G)).X
  recovers : point ≫ (identityComponentι ((baseChange q).obj G)).hom.hom =
    d.fieldSection hg q
  relation : PointwiseSchemeAction.IsTransporter
    (fieldIdentityTorusHom I G q i₁) (fieldIdentityTorusHom I G q i₂) point

/-- On the supplied open neighbourhood, construct the actual transporter
point inside every actual field identity component. -/
def fieldIdentityTransporterData {K : Type u} [Field K]
    (q : Spec (CommRingCat.of K) ⟶ S)
    (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    FieldIdentityTransporterData I G d hg i₁ i₂ q where
  point := d.fieldIdentityPoint hg q hq
  recovers := d.fieldIdentityPoint_comp hg q hq
  relation := by
    apply PointwiseSchemeAction.IsTransporter.of_comp
      (identityComponentι ((baseChange q).obj G))
    simpa only [fieldIdentityTorusHom_comp,
      RelativeIdentityComponent.SectionIdentityNeighbourhoodData.fieldIdentityPoint_comp] using
      fieldSection_isTransporter I G d hg i₁ i₂ htrans q

/-- Specialize to the exact chosen geometric point over an original base
point, with target the actual geometric identity-component group. -/
def geometricIdentityTransporterData (t : S) (ht : t ∈ d.neighbourhood) :
    FieldIdentityTransporterData I G d hg i₁ i₂ (geometricPoint S t) :=
  fieldIdentityTransporterData I G d hg i₁ i₂ htrans (geometricPoint S t)
    (d.range_geometricPoint_subset t ht)

/-- The actual geometric transporter point recovers the original section at
the original base point, as an equality of scheme morphisms. -/
@[reassoc]
theorem geometricIdentityTransporterData_recovers (t : S) (ht : t ∈ d.neighbourhood) :
    (geometricIdentityTransporterData I G d hg i₁ i₂ htrans t ht).point.left ≫
        (identityComponentι (geometricFiber G t)).hom.hom.left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (geometricPoint S t) =
      geometricPoint S t ≫ g :=
  d.geometricIdentityPoint_recovers hg t ht

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme.splitTorus

variable {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  {K : Type u} [Field K] (q : Spec (CommRingCat.of K) ⟶ S)

/-- Factoring the torus into the actual field identity component respects an
integral-coordinate automorphism of that torus. -/
theorem fieldIdentityTorusHom_comp_exponentIso
    (i : splitTorus S I ⟶ G) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    fieldIdentityTorusHom I G q ((exponentIso S I e).hom ≫ i) =
      (exponentIso (Spec (CommRingCat.of K)) I e).hom ≫ fieldIdentityTorusHom I G q i := by
  apply (cancel_mono (identityComponentι ((baseChange q).obj G))).mp
  simp only [Category.assoc, fieldIdentityTorusHom_comp]
  have he := exponentIso_baseChange S I q e
  have he' : (baseChangeIso q I).inv ≫ (baseChange q).map (exponentIso S I e).hom =
      (exponentIso (Spec (CommRingCat.of K)) I e).hom ≫ (baseChangeIso q I).inv := by
    apply (cancel_mono (baseChangeIso q I).hom).mp
    rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f => f ≫ (baseChange q).map i) he'

variable {g : S ⟶ G.X.left} {s : S}
  (d : RelativeIdentityComponent.SectionIdentityNeighbourhoodData G g s)
  (hg : g ≫ G.X.hom = 𝟙 S) (i : splitTorus S I ⟶ G)
  (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
  (htrans : PointwiseSchemeAction.IsTransporter ((exponentIso S I e).hom ≫ i) i
    (show Over.mk (𝟙 S) ⟶ G.X from Over.homMk g hg))

/-- The constructed identity-component transporter, as an actual coefficient
point in the convention of the rank-one field criterion. -/
def fieldAffineIdentityTransporterPoint
    (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    Lie.AffinePoints (identityComponent ((baseChange q).obj G)) K :=
  CategoryTheory.CartesianMonoidalCategory.toUnit _ ≫
    (fieldIdentityTransporterData I G d hg ((exponentIso S I e).hom ≫ i) i htrans q hq).point

/-- The field point realizes the specified integral-coordinate automorphism
on the actual torus inside the actual field identity component, on every test. -/
theorem fieldAffineIdentityTransporterPoint_relation
    (hq : Set.range q ⊆ (d.neighbourhood : Set S)) :
    PointwiseSchemeAction.IsTransporter
      ((exponentIso (Spec (CommRingCat.of K)) I e).hom ≫ fieldIdentityTorusHom I G q i)
      (fieldIdentityTorusHom I G q i)
      (fieldAffineIdentityTransporterPoint I G q d hg i e htrans hq) := by
  have h := (fieldIdentityTransporterData I G d hg
    ((exponentIso S I e).hom ≫ i) i htrans q hq).relation
  rw [fieldIdentityTorusHom_comp_exponentIso] at h
  exact h.restrict (CategoryTheory.CartesianMonoidalCategory.toUnit _)

end Langlands.GroupScheme.splitTorus
