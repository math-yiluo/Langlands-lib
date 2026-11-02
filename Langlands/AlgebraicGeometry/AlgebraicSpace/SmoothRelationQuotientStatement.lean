import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # The canonical etale quotient of a smooth algebraic-space relation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A presheaf map is smooth when all its scheme base changes are represented
by smooth morphisms of actual schemes. -/
def IsSmooth {S : Scheme.{u}} {F G : Presheaf S} (a : F ⟶ G) : Prop :=
  (MorphismProperty.inverseImage (@Smooth.{u}) (Over.forget S)).relative
    (schemeYoneda S) a

/-- Smooth transformations are represented by schemes on every scheme test. -/
theorem IsSmooth.representable {S : Scheme.{u}} {F G : Presheaf S} {a : F ⟶ G}
    (ha : IsSmooth a) : IsRepresentableMorphism a := ha.1

/-- Every actual projection in a represented base change of a smooth map is smooth. -/
theorem IsSmooth.projection {S : Scheme.{u}} {F G : Presheaf S} {a : F ⟶ G}
    (ha : IsSmooth a) {T V : Over S} (g : (schemeYoneda S).obj T ⟶ G)
    (b : (schemeYoneda S).obj V ⟶ F) (p : V ⟶ T)
    (h : IsPullback b ((schemeYoneda S).map p) a g) : Smooth p.left :=
  ha.2 g b p h

namespace SmoothRelationQuotient

variable {S : Scheme.{u}} {U : Over S} (R : AlgebraicSpace S)
  (s t : R.presheaf ⟶ (schemeYoneda S).obj U)

/-- The relation on the full scheme-point type, witnessed by an actual section
of the arrow algebraic space. -/
def relation (T : Over S) (x y : ((schemeYoneda S).obj U).obj (op T)) : Prop :=
  ∃ r : R.sections T, s.app (op T) r = x ∧ t.app (op T) r = y

/-- The arrow sheaf is a monomorphic equivalence relation on every scheme test. -/
def IsEquivalenceRelation : Prop :=
  ∀ T : Over S,
    Function.Injective (fun r : R.sections T ↦ (s.app (op T) r, t.app (op T) r)) ∧
      Equivalence (relation R s t T)

variable (h : IsEquivalenceRelation R s t)

/-- The setoid on all scheme points, with no restriction to geometric points. -/
def pointSetoid (T : Over S) : Setoid (((schemeYoneda S).obj U).obj (op T)) where
  r := relation R s t T
  iseqv := (h T).2

/-- Restriction preserves the relation by restricting its actual arrow section. -/
lemma relation_map {T V : Over S} (g : V ⟶ T)
    {x y : ((schemeYoneda S).obj U).obj (op T)} (hxy : relation R s t T x y) :
    relation R s t V (((schemeYoneda S).obj U).map g.op x)
      (((schemeYoneda S).obj U).map g.op y) := by
  obtain ⟨r, rfl, rfl⟩ := hxy
  refine ⟨R.presheaf.map g.op r, ?_, ?_⟩
  · exact NatTrans.naturality_apply s g.op r
  · exact NatTrans.naturality_apply t g.op r

/-- The actual presheaf of pointwise equivalence classes. -/
def quotientPresheaf : Presheaf S where
  obj T := Quotient (pointSetoid R s t h T.unop)
  map g := ↾(Quotient.map (((schemeYoneda S).obj U).map g)
    (fun _ _ hxy ↦ relation_map R s t g.unop hxy))
  map_id T := by
    ext q
    induction q using Quotient.ind with
    | _ x => exact congrArg (Quotient.mk _) (((schemeYoneda S).obj U).map_id_apply T x)
  map_comp g k := by
    ext q
    induction q using Quotient.ind with
    | _ x =>
      exact congrArg (Quotient.mk _) (((schemeYoneda S).obj U).map_comp_apply g k x)

/-- The canonical map from scheme points to their pointwise classes. -/
def toQuotientPresheaf : (schemeYoneda S).obj U ⟶ quotientPresheaf R s t h where
  app T := ↾(Quotient.mk (pointSetoid R s t h T.unop))
  naturality _ _ _ := rfl

/-- The canonical quotient is the etale sheafification of all pointwise classes. -/
def quotientSheaf : Sheaf (Scheme.etaleTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.etaleTopology.over S) (Type (u + 1))).obj
    (quotientPresheaf R s t h)

/-- The fixed canonical map to the etale quotient. -/
def quotientMap : (schemeYoneda S).obj U ⟶ (quotientSheaf R s t h).obj :=
  toQuotientPresheaf R s t h ≫
    toSheafify (Scheme.etaleTopology.over S) (quotientPresheaf R s t h)

/-- Smoothness of both projections expressed on an actual surjective etale
scheme atlas of the arrow algebraic space. -/
def HasSmoothProjections : Prop :=
  ∃ (W : Over S) (b : (schemeYoneda S).obj W ⟶ R.presheaf) (s₀ t₀ : W ⟶ U),
    IsEtale b ∧ IsSurjective b ∧
      b ≫ s = (schemeYoneda S).map s₀ ∧
      b ≫ t = (schemeYoneda S).map t₀ ∧ Smooth s₀.left ∧ Smooth t₀.left

end SmoothRelationQuotient

open SmoothRelationQuotient

/-- The smooth special case of the general relation quotient theorem, with
canonical etale quotient, full effectiveness and a locally finite type atlas. -/
def SmoothRelationQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S) (R : AlgebraicSpace S)
    (s t : R.presheaf ⟶ (schemeYoneda S).obj U)
    (h : IsEquivalenceRelation R s t),
    HasSmoothProjections R s t → LocallyOfFiniteType U.hom →
      Presheaf.IsSheaf (fppfTopology S) (quotientSheaf R s t h).obj ∧
      HasRepresentableDiagonal (quotientSheaf R s t h).obj ∧
      IsPullback s t (quotientMap R s t h) (quotientMap R s t h) ∧
      IsSmooth (quotientMap R s t h) ∧ IsSurjective (quotientMap R s t h) ∧
      ∃ (V : Over S) (a : (schemeYoneda S).obj V ⟶ (quotientSheaf R s t h).obj),
        IsEtale a ∧ IsSurjective a ∧ LocallyOfFiniteType V.hom

end Langlands.AlgebraicGeometry.AlgebraicSpace
