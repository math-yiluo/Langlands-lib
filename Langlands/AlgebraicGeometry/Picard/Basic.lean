import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Langlands.CategoryTheory.Picard.Basic
import Langlands.CategoryTheory.Picard.TensorEquivalenceProof

/-!
# Invertible sheaves and the scheme Picard group

The tensor and pullback are the actual published scheme-module constructions.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.Picard

variable (X : Scheme.{u})

/-- Tensor-inverse existence agrees with invertibility by tensoring equivalence. -/
lemma tensorInvertible_iff_tensorLeft_isEquivalence (M : X.Modules) :
    Langlands.CategoryTheory.TensorInvertible M ↔ (tensorLeft M).IsEquivalence :=
  Langlands.CategoryTheory.Picard.tensorInvertibilityEquivalence X.Modules M

/-- Sheaves possessing a tensor inverse. -/
abbrev InvertibleSheaf : Type (u + 1) :=
  ObjectProperty.FullSubcategory (Langlands.CategoryTheory.TensorInvertible
    (C := X.Modules))

namespace InvertibleSheaf

/-- The underlying sheaf of modules. -/
def forget : InvertibleSheaf X ⥤ X.Modules :=
  ObjectProperty.ι (Langlands.CategoryTheory.TensorInvertible (C := X.Modules))

/-- The tensor unit as an invertible sheaf. -/
def trivial : InvertibleSheaf X :=
  ⟨𝟙_ X.Modules, Langlands.CategoryTheory.TensorInvertible.unit⟩

variable {X}

/-- Transport an invertible sheaf structure across a sheaf isomorphism. -/
def ofIso (L : InvertibleSheaf X) {M : X.Modules} (e : L.obj ≅ M) :
    InvertibleSheaf X :=
  ⟨M, Langlands.CategoryTheory.TensorInvertible.of_iso e L.property⟩

/-- Tensor product of invertible sheaves, in the actual module category. -/
def tensor (L M : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨L.obj ⊗ M.obj, L.property.tensor M.property⟩

/-- A chosen inverse sheaf. -/
def inverse (L : InvertibleSheaf X) : InvertibleSheaf X :=
  ⟨L.property.choose,
    ⟨L.obj, ⟨β_ _ _ ≪≫ L.property.choose_spec.some⟩⟩⟩

/-- Evaluation of a sheaf against its chosen tensor inverse. -/
def tensorInverseIso (L : InvertibleSheaf X) :
    L.obj ⊗ L.inverse.obj ≅ 𝟙_ X.Modules :=
  L.property.choose_spec.some

end InvertibleSheaf

/-- The abelian group of isomorphism classes of tensor-invertible module sheaves. -/
abbrev Group : Type (u + 1) := Langlands.CategoryTheory.PicardGroup X.Modules

/-- The class of an invertible sheaf. -/
def classOf (L : InvertibleSheaf X) : Group X :=
  Langlands.CategoryTheory.PicardGroup.ofObject L.obj L.property

namespace Group

/-- A chosen invertible sheaf representing a class. -/
def representative (x : Group X) : InvertibleSheaf X :=
  ⟨Langlands.CategoryTheory.PicardGroup.representative x,
    Langlands.CategoryTheory.PicardGroup.representative_invertible x⟩

@[simp] lemma classOf_representative (x : Group X) :
    classOf X (representative X x) = x :=
  Langlands.CategoryTheory.PicardGroup.ofObject_representative x

end Group

lemma classOf_eq_iff (L M : InvertibleSheaf X) :
    classOf X L = classOf X M ↔ Nonempty (L.obj ≅ M.obj) :=
  Langlands.CategoryTheory.PicardGroup.ofObject_eq_iff _ _ _ _

@[simp] lemma classOf_trivial : classOf X (InvertibleSheaf.trivial X) = 0 :=
  Langlands.CategoryTheory.PicardGroup.ofObject_unit

lemma classOf_tensor (L M : InvertibleSheaf X) :
    classOf X (L.tensor M) = classOf X L + classOf X M :=
  Langlands.CategoryTheory.PicardGroup.ofObject_tensor _ _ _ _

lemma classOf_inverse (L : InvertibleSheaf X) :
    classOf X L.inverse = -classOf X L := by
  apply eq_neg_of_add_eq_zero_left
  rw [← classOf_tensor]
  exact (classOf_eq_iff X _ _).mpr ⟨β_ _ _ ≪≫ L.tensorInverseIso⟩ |>.trans
    (classOf_trivial X)

section Pullback

variable {X} {Y : Scheme.{u}} (f : X ⟶ Y)

/-- Pullback of invertible sheaves using Mathlib's module pullback functor. -/
def InvertibleSheaf.pullback : InvertibleSheaf Y ⥤ InvertibleSheaf X where
  obj L := ⟨(Scheme.Modules.pullback f).obj L.obj, L.property.map _⟩
  map g := ObjectProperty.homMk ((Scheme.Modules.pullback f).map g.hom)
  map_id L := by apply ObjectProperty.hom_ext; simp
  map_comp g h := by apply ObjectProperty.hom_ext; simp

/-- The homomorphism induced by actual module pullback. -/
def Group.pullback : Group Y →+ Group X :=
  Langlands.CategoryTheory.PicardGroup.map (Scheme.Modules.pullback f)

lemma Group.pullback_classOf (L : InvertibleSheaf Y) :
    Group.pullback f (classOf Y L) =
      classOf X ((InvertibleSheaf.pullback f).obj L) :=
  Langlands.CategoryTheory.PicardGroup.map_ofObject _ _ _

end Pullback

end Langlands.AlgebraicGeometry.Picard
