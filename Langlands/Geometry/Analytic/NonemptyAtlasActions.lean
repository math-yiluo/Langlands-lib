import Langlands.Geometry.Analytic.AtlasNonemptyCharts
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Full categories of actions with nonempty supplied atlas charts -/

noncomputable section

universe u v w z t

namespace Langlands.Analytic

open CategoryTheory

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (M : Type z) [Monoid M]

/-- Every supplied chart has nonempty bounded multiplicative spectrum. -/
def nonemptyAtlasActionProperty :
    ObjectProperty (Action (AffinoidAtlasPresentation.{u, v, w} K) M) :=
  fun X => X.V.atlas.HasNonemptyCharts

/-- The full category retains every original bounded equivariant arrow. -/
abbrev NonemptyAtlasAction :=
  (nonemptyAtlasActionProperty.{u, v, w, z} K M).FullSubcategory

namespace NonemptyAtlasAction

variable {K M}

/-- Forget only the nonempty-chart condition. -/
def inclusion : NonemptyAtlasAction.{u, v, w, z} K M ⥤
    Action (AffinoidAtlasPresentation.{u, v, w} K) M :=
  (nonemptyAtlasActionProperty K M).ι

instance : (inclusion (K := K) (M := M)).Full :=
  inferInstanceAs (nonemptyAtlasActionProperty K M).ι.Full

instance : (inclusion (K := K) (M := M)).Faithful :=
  inferInstanceAs (nonemptyAtlasActionProperty K M).ι.Faithful

/-- The existing same-space normalization lands in the full subcategory. -/
def normalize :
    Action (AffinoidAtlasPresentation.{u, v, w} K) M ⥤
      NonemptyAtlasAction.{u, v, w, z} K M :=
  (nonemptyAtlasActionProperty K M).lift
    (AffinoidAtlasPresentation.nonemptyActionFunctor M)
    (fun X => X.V.atlas.nonemptySubatlas_hasNonemptyCharts)

/-- Forgetting the condition recovers the precise original normalization functor. -/
theorem normalize_inclusion :
    normalize (K := K) (M := M) ⋙ inclusion =
      AffinoidAtlasPresentation.nonemptyActionFunctor M := rfl

/-- Normalization is invertible for these actions, using their actual chart condition. -/
def normalizationIso (X : NonemptyAtlasAction.{u, v, w, z} K M) :
    (AffinoidAtlasPresentation.nonemptyActionFunctor M).obj X.obj ≅ X.obj :=
  Action.mkIso (X.obj.V.nonemptyIso X.property)
    (fun m => (X.obj.ρ m).nonemptyMap_nonemptyInclusion)

/-- Naturality is an equality of complete equivariant bounded atlas arrows. -/
theorem normalizationIso_naturality
    {X Y : NonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    (AffinoidAtlasPresentation.nonemptyActionFunctor M).map f.hom ≫
        (normalizationIso Y).hom =
      (normalizationIso X).hom ≫ f.hom :=
  Action.Hom.ext f.hom.hom.nonemptyMap_nonemptyInclusion

/-- The canonical normalization is naturally isomorphic to the original inclusion. -/
def normalizationNatIso :
    inclusion (K := K) (M := M) ⋙
        AffinoidAtlasPresentation.nonemptyActionFunctor M ≅ inclusion :=
  NatIso.ofComponents normalizationIso (fun f => normalizationIso_naturality f)

/-- The actual inverse chart map is natural as well. -/
theorem normalizationIso_inv_naturality
    {X Y : NonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    f.hom ≫ (normalizationIso Y).inv =
      (normalizationIso X).inv ≫
        (AffinoidAtlasPresentation.nonemptyActionFunctor M).map f.hom :=
  (normalizationNatIso (K := K) (M := M)).inv.naturality f

@[simp]
theorem normalizationIso_hom_hom (X : NonemptyAtlasAction.{u, v, w, z} K M) :
    (normalizationIso X).hom.hom = X.obj.V.nonemptyInclusion := rfl

@[simp]
theorem normalizationIso_inv_hom (X : NonemptyAtlasAction.{u, v, w, z} K M) :
    (normalizationIso X).inv.hom = X.obj.V.nonemptyInv X.property := rfl

/-- Every original chart survives, so the inverse retains its original index. -/
@[simp]
theorem normalizationIso_inv_indexMap (X : NonemptyAtlasAction.{u, v, w, z} K M)
    (i : X.obj.V.atlas.Index) :
    (normalizationIso X).inv.hom.indexMap i = ⟨i, X.property i⟩ := rfl

/-- The inverse uses actual bounded identities on the original chart algebras. -/
@[simp]
theorem normalizationIso_inv_pullback (X : NonemptyAtlasAction.{u, v, w, z} K M)
    (i : X.obj.V.atlas.Index) :
    (normalizationIso X).inv.hom.pullback i =
      BoundedAlgHom.id K (X.obj.V.atlas.algebra i) := rfl

variable {N : Type t} [Monoid N]

/-- Restrict the action parameter without changing any charts or bounded maps. -/
def restrict (φ : N →* M) :
    NonemptyAtlasAction.{u, v, w, z} K M ⥤
      NonemptyAtlasAction.{u, v, w, t} K N :=
  (nonemptyAtlasActionProperty K N).lift
    (inclusion ⋙ Action.res (AffinoidAtlasPresentation.{u, v, w} K) φ)
    (fun X => X.property)

@[simp]
theorem restrict_obj_V (φ : N →* M)
    (X : NonemptyAtlasAction.{u, v, w, z} K M) :
    ((restrict φ).obj X).obj.V = X.obj.V := rfl

@[simp]
theorem restrict_map_hom (φ : N →* M)
    {X Y : NonemptyAtlasAction.{u, v, w, z} K M} (f : X ⟶ Y) :
    ((restrict φ).map f).hom.hom = f.hom.hom := rfl

end NonemptyAtlasAction

end Langlands.Analytic
