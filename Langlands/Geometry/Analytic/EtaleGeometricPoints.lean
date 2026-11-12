import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.EtaleSite
import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Fibre functors of field-valued points on the étale site -/

noncomputable section

universe w₁ w₂ v₁ u₁ u v uL

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] (F : C ⥤ Type w₁)

/-- The category of elements does not change when the values of a functor to types are lifted
to a larger universe. -/
def elementsULiftEquivalence : F.Elements ≌ (F ⋙ uliftFunctor.{w₂, w₁}).Elements where
  functor :=
    { obj e := Functor.elementsMk _ e.obj (ULift.up e.val)
      map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val) }
  inverse :=
    { obj e := Functor.elementsMk _ e.obj e.val.down
      map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val) }
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => by ext; exact (Category.comp_id _).trans (Category.id_comp _).symm)

end CategoryTheory.Functor

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type uL) [NormedField L] [NormedAlgebra K L]

namespace EtaleSite

variable {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- The fibre functor of an `L`-valued point `x` of `X`: an étale `U ⟶ X` goes to the set of
`L`-valued points of `U` lying over `x`. -/
def pointFibre (x : (localizedFieldPointFunctor L).obj X) : EtaleSite X ⥤ Type (max u v uL) where
  obj U := {p : (localizedFieldPointFunctor L).obj U.left //
    (localizedFieldPointFunctor L).map U.hom p = x}
  map {U V} f := TypeCat.ofHom fun p => ⟨(localizedFieldPointFunctor L).map f.left p.1, by
    rw [← Functor.map_comp_apply, MorphismProperty.Over.w f]
    exact p.2⟩
  map_id U := by
    ext p
    exact (localizedFieldPointFunctor L).map_id_apply U.left p.1
  map_comp f g := by
    ext p
    exact (localizedFieldPointFunctor L).map_comp_apply f.left g.left p.1

/-- The point axioms for the fibre functor at `x`: its category of elements is cofiltered, and
every element over an object is the image of an element over a member of each covering
sieve. -/
def PointAxioms (x : (localizedFieldPointFunctor L).obj X) : Prop :=
  IsCofiltered (pointFibre L x).Elements ∧
    ∀ {U : EtaleSite X} (R : Sieve U), R ∈ etaleTopology X U → ∀ p : (pointFibre L x).obj U,
      ∃ (V : EtaleSite X) (f : V ⟶ U) (_ : R f) (q : (pointFibre L x).obj V),
        (pointFibre L x).map f q = p

/-- The point of the étale site given by an `L`-valued point satisfying the point axioms. The
fibre functor is lifted to the universe of `Ét(X)`, so that its category of elements is
small. -/
def toPoint (x : (localizedFieldPointFunctor L).obj X) (h : PointAxioms L x) :
    (etaleTopology X).Point.{max u (v + 1) uL} where
  fiber := pointFibre L x ⋙ uliftFunctor.{max u (v + 1) uL, max u v uL}
  isCofiltered :=
    have := h.1
    IsCofiltered.of_equivalence (Functor.elementsULiftEquivalence _)
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR p := by
    obtain ⟨V, f, hf, q, hq⟩ := h.2 R hR p.down
    exact ⟨V, f, hf, ULift.up q, congrArg ULift.up hq⟩

@[simp]
theorem toPoint_fiber (x : (localizedFieldPointFunctor L).obj X) (h : PointAxioms L x) :
    (toPoint L x h).fiber = pointFibre L x ⋙ uliftFunctor.{max u (v + 1) uL, max u v uL} :=
  rfl

/-- Translation along `e : X ≅ Y` identifies the fibre over the image of `x` with the fibre
over `x`: the points of `U ⟶ X ⟶ Y` over `e(x)` are the points of `U` over `x`. -/
def pointFibreTranslate (e : X ≅ Y) (x : (localizedFieldPointFunctor L).obj X) :
    (translate e).functor ⋙ pointFibre L ((localizedFieldPointFunctor L).map e.hom x) ≅
      pointFibre L x :=
  NatIso.ofComponents
    (fun U => (Equiv.subtypeEquivRight fun p => by
      change (localizedFieldPointFunctor L).map (U.hom ≫ e.hom) p = _ ↔ _
      rw [Functor.map_comp]
      exact ((localizedFieldPointFunctor L).mapIso e).toEquiv.injective.eq_iff).toIso)
    (fun _ => rfl)

/-- The lifted form of `pointFibreTranslate`, for the fibre functors of the points. -/
def pointTranslate (e : X ≅ Y) (x : (localizedFieldPointFunctor L).obj X)
    (hx : PointAxioms L x) (he : PointAxioms L ((localizedFieldPointFunctor L).map e.hom x)) :
    (translate e).functor ⋙ (toPoint L _ he).fiber ≅ (toPoint L x hx).fiber :=
  Functor.isoWhiskerRight (pointFibreTranslate L e x) uliftFunctor.{max u (v + 1) uL, max u v uL}

end EtaleSite

end Langlands.Analytic.SaturatedAtlasPresentation
