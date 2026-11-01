import Langlands.Geometry.Analytic.NonemptyAtlasActions
import Langlands.CategoryTheory.TopCatSelfForget

/-! # Full nonempty-chart atlas action categories with joint point continuity -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (M : Type z) [Monoid M] [TopologicalSpace M]

/-- The original charts have nonempty spectra and the original point action is continuous. -/
def pointContinuousNonemptyAtlasActionProperty :
    ObjectProperty (Action (AffinoidAtlasPresentation.{u, v, w} K) M) :=
  fun X => X.V.atlas.HasNonemptyCharts ∧
    Continuous (fun p : M × X.V.space => (X.ρ p.1).baseMap p.2)

-- The category's sort combines the independent point and chart-index universes.
set_option linter.checkUnivs false in
/-- All complete equivariant bounded arrows between the specified continuous actions. -/
abbrev PointContinuousNonemptyAtlasAction : Type _ :=
  (pointContinuousNonemptyAtlasActionProperty.{u, v, w, z} K M).FullSubcategory

namespace PointContinuousNonemptyAtlasAction

variable {K M}

/-- Retain the entire original categorical action and every complete arrow. -/
def inclusion : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M ⥤
    Action (AffinoidAtlasPresentation.{u, v, w} K) M :=
  (pointContinuousNonemptyAtlasActionProperty K M).ι

instance : (inclusion (K := K) (M := M)).Full :=
  inferInstanceAs (pointContinuousNonemptyAtlasActionProperty K M).ι.Full

instance : (inclusion (K := K) (M := M)).Faithful :=
  inferInstanceAs (pointContinuousNonemptyAtlasActionProperty K M).ι.Faithful

/-- Forget point continuity, keeping the original nonempty-chart action. -/
def toNonempty : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M ⥤
    NonemptyAtlasAction.{u, v, w, z} K M :=
  (nonemptyAtlasActionProperty K M).lift inclusion (fun X => X.property.1)

theorem toNonempty_inclusion :
    toNonempty (K := K) (M := M) ⋙ NonemptyAtlasAction.inclusion = inclusion := rfl

theorem continuous_action (X : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M) :
    Continuous (fun p : M × X.obj.V.space => (X.obj.ρ p.1).baseMap p.2) :=
  X.property.2

/-- Realize the precise given point action in Mathlib's continuous action category. -/
def realization : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M ⥤
    ContAction TopCat.{v} M :=
  (Action.isContinuous TopCat M).lift
    (inclusion ⋙ AffinoidAtlasPresentation.spaceFunctor.mapAction M)
    (fun X => (Action.isContinuous_def _).mpr X.continuous_action)

@[simp]
theorem realization_obj_space
    (X : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M) :
    (realization.obj X).obj.V = X.obj.V.space := rfl

@[simp]
theorem realization_map_hom
    {X Y : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    (realization.map f).hom.hom = TopCat.ofHom f.hom.hom.baseMap := rfl

/-- Normalization retains the original continuous point action on the same space. -/
def normalize : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M ⥤
    PointContinuousNonemptyAtlasAction.{u, v, w, z} K M :=
  (pointContinuousNonemptyAtlasActionProperty K M).lift
    (inclusion ⋙ AffinoidAtlasPresentation.nonemptyActionFunctor M)
    (fun X => ⟨X.obj.V.atlas.nonemptySubatlas_hasNonemptyCharts, X.continuous_action⟩)

/-- The inverse uses the explicit condition on every original chart. -/
def normalizationIso (X : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M) :
    normalize.obj X ≅ X :=
  ObjectProperty.isoMk _ (NonemptyAtlasAction.normalizationIso (toNonempty.obj X))

theorem normalizationIso_naturality
    {X Y : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    normalize.map f ≫ (normalizationIso Y).hom =
      (normalizationIso X).hom ≫ f := by
  apply ObjectProperty.hom_ext
  exact NonemptyAtlasAction.normalizationIso_naturality (toNonempty.map f)

/-- Jointly continuous normalization is naturally isomorphic to the original functor. -/
def normalizationNatIso :
    normalize (K := K) (M := M) ≅ 𝟭 _ :=
  NatIso.ofComponents normalizationIso (fun f => normalizationIso_naturality f)

variable {N : Type t} [Monoid N] [TopologicalSpace N]

/-- Precompose by a continuous monoid homomorphism, retaining all original atlas data. -/
def restrict (φ : N →ₜ* M) :
    PointContinuousNonemptyAtlasAction.{u, v, w, z} K M ⥤
      PointContinuousNonemptyAtlasAction.{u, v, w, t} K N :=
  (pointContinuousNonemptyAtlasActionProperty K N).lift
    (inclusion ⋙ Action.res (AffinoidAtlasPresentation.{u, v, w} K) φ.toMonoidHom)
    (fun X => ⟨X.property.1,
      X.continuous_action.comp ((φ.continuous.comp continuous_fst).prodMk continuous_snd)⟩)

@[simp]
theorem restrict_obj_V (φ : N →ₜ* M)
    (X : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M) :
    ((restrict φ).obj X).obj.V = X.obj.V := rfl

@[simp]
theorem restrict_obj_action (φ : N →ₜ* M)
    (X : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M) (n : N) :
    ((restrict φ).obj X).obj.ρ n = X.obj.ρ (φ n) := rfl

@[simp]
theorem restrict_map_hom (φ : N →ₜ* M)
    {X Y : PointContinuousNonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    ((restrict φ).map f).hom.hom = f.hom.hom := rfl

theorem restrict_toNonempty (φ : N →ₜ* M) :
    restrict (K := K) φ ⋙ toNonempty =
      toNonempty ⋙ NonemptyAtlasAction.restrict φ.toMonoidHom := rfl

end PointContinuousNonemptyAtlasAction

end Langlands.Analytic
