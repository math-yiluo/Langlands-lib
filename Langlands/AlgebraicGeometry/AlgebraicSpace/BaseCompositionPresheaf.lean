import Langlands.AlgebraicGeometry.AlgebraicSpace.OriginalBaseTransport

/-! # Composing the base of a relative presheaf -/

universe u

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition

open OriginalBaseTransport

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- A section over `V/T` is a structure map `V.left ⟶ S`, a section over it,
and the equation that its composite to `T` is `V.hom`. -/
def presheaf (F : Presheaf S) : Presheaf T :=
  fiberPresheaf (totalToBase F ≫ CategoryTheory.uliftYoneda.{u + 1}.map g)

/-- A morphism retains the structure map to the original base. -/
def map {F G : Presheaf S} (f : F ⟶ G) : presheaf g F ⟶ presheaf g G where
  app V := TypeCat.ofHom fun x => ⟨⟨x.val.1, f.app (op (Over.mk x.val.1)) x.val.2⟩,
    x.property⟩
  naturality {V W} a := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (Sigma.mk (a.unop.left ≫ x.val.1))
      (f.naturality_apply
        (Over.homMk a.unop.left rfl :
          Over.mk (a.unop.left ≫ x.val.1) ⟶ Over.mk x.val.1).op x.val.2)

/-- Composition of bases acts functorially on relative presheaves. -/
def presheafFunctor : Presheaf S ⥤ Presheaf T where
  obj := presheaf g
  map := map g
  map_id F := by
    ext V x
    apply Subtype.ext
    rfl
  map_comp f h := by
    ext V x
    apply Subtype.ext
    rfl

/-- A section with a fixed original structure map gives a section over the composed base. -/
def liftSection (F : Presheaf S) (U : Over S) (x : F.obj (op U)) :
    (presheaf g F).obj (op ((Over.map g).obj U)) :=
  ⟨⟨U.hom, x⟩, rfl⟩

lemma liftSection_injective (F : Presheaf S) (U : Over S) :
    Function.Injective (liftSection g F U) := by
  intro x y h
  exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2

@[simp]
lemma map_liftSection {F G : Presheaf S} (f : F ⟶ G) (U : Over S)
    (x : F.obj (op U)) :
    (map g f).app (op ((Over.map g).obj U)) (liftSection g F U x) =
      liftSection g G U (f.app (op U) x) := rfl

/-- Equality to a target with fixed structure map forces the source structure map to agree. -/
lemma structure_eq_of_map_eq_liftSection {F G : Presheaf S} (f : F ⟶ G) (U : Over S)
    (y : G.obj (op U)) (x : (presheaf g F).obj (op ((Over.map g).obj U)))
    (h : (map g f).app _ x = liftSection g G U y) : x.val.1 = U.hom :=
  congrArg (fun z => z.val.1) h

/-- The map from the original point fibre to the fibre after composition of bases. -/
def fibreMap {F G : Presheaf S} (f : F ⟶ G) (U : Over S) (y : G.obj (op U)) :
    {x : F.obj (op U) // f.app (op U) x = y} →
      {x : (presheaf g F).obj (op ((Over.map g).obj U)) //
        (map g f).app _ x = liftSection g G U y} :=
  fun x => ⟨liftSection g F U x.val, by rw [map_liftSection, x.property]⟩

lemma fibreMap_bijective {F G : Presheaf S} (f : F ⟶ G) (U : Over S)
    (y : G.obj (op U)) : Function.Bijective (fibreMap g f U y) := by
  constructor
  · intro x z h
    apply Subtype.ext
    exact liftSection_injective g F U (congrArg Subtype.val h)
  · rintro ⟨⟨⟨s, x⟩, hs⟩, hx⟩
    have hs' : s = U.hom := congrArg (fun z => z.val.1) hx
    subst s
    have hx' : f.app (op U) x = y :=
      eq_of_heq (Sigma.mk.inj (congrArg Subtype.val hx)).2
    exact ⟨⟨x, hx'⟩, rfl⟩

/-- Composition of bases preserves each point fibre above an original target section. -/
def fibreEquiv {F G : Presheaf S} (f : F ⟶ G) (U : Over S) (y : G.obj (op U)) :
    {x : F.obj (op U) // f.app (op U) x = y} ≃
      {x : (presheaf g F).obj (op ((Over.map g).obj U)) //
        (map g f).app _ x = liftSection g G U y} :=
  Equiv.ofBijective (fibreMap g f U y) (fibreMap_bijective g f U y)

lemma card_fibre {F G : Presheaf S} (f : F ⟶ G) (U : Over S) (y : G.obj (op U)) :
    Nat.card {x : F.obj (op U) // f.app (op U) x = y} =
      Nat.card {x : (presheaf g F).obj (op ((Over.map g).obj U)) //
        (map g f).app _ x = liftSection g G U y} :=
  Nat.card_congr (fibreEquiv g f U y)

end Langlands.AlgebraicGeometry.AlgebraicSpace.BaseComposition
