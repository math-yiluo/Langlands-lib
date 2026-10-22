import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Abelian schemes with explicit commutativity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

/-- The source definition: a smooth proper group scheme with geometrically connected fibres. -/
def GroupScheme.IsAbelian {S : Scheme.{u}} (G : GroupScheme S) : Prop :=
  Smooth G.X.hom ∧ IsProper G.X.hom ∧ GeometricallyConnected G.X.hom

/-- An abelian scheme with commutativity explicit. Equivalence with the source definition
is a separate proposition and is not assumed by this bundle. -/
structure AbelianScheme (S : Scheme.{u}) extends CommGroupScheme S where
  [smooth : Smooth X.hom]
  [proper : IsProper X.hom]
  [geometricallyConnected : GeometricallyConnected X.hom]

attribute [instance] AbelianScheme.smooth AbelianScheme.proper
  AbelianScheme.geometricallyConnected

namespace AbelianScheme

variable {S T : Scheme.{u}}

/-- Homomorphisms are the actual homomorphisms of the underlying commutative group schemes. -/
instance : Category (AbelianScheme S) where
  Hom A B := A.toCommGroupScheme ⟶ B.toCommGroupScheme
  id A := 𝟙 A.toCommGroupScheme
  comp f g := f ≫ g
  id_comp := by intro A B f; exact Category.id_comp (obj := CommGroupScheme S) f
  comp_id := by intro A B f; exact Category.comp_id (obj := CommGroupScheme S) f
  assoc := by intro A B C D f g h; exact Category.assoc (obj := CommGroupScheme S) f g h

/-- The homomorphism of underlying commutative group schemes. -/
abbrev commHom {A B : AbelianScheme S} (f : A ⟶ B) :
    A.toCommGroupScheme ⟶ B.toCommGroupScheme := f

instance (A B : AbelianScheme S) : AddCommGroup (A ⟶ B) :=
  inferInstanceAs (AddCommGroup (A.toCommGroupScheme ⟶ B.toCommGroupScheme))

instance : Preadditive (AbelianScheme S) where
  add_comp := by
    intro A B C f g h
    exact Preadditive.add_comp _ _ _ (commHom f) (commHom g) (commHom h)
  comp_add := by
    intro A B C f g h
    exact Preadditive.comp_add _ _ _ (commHom f) (commHom g) (commHom h)

/-- The underlying homomorphism of group objects. -/
abbrev groupHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toGrp ⟶ B.toGrp :=
  CommGroupScheme.groupHom (commHom f)

/-- The underlying scheme morphism. -/
abbrev hom {A B : AbelianScheme S} (f : A ⟶ B) : A.X.left ⟶ B.X.left :=
  CommGroupScheme.hom (commHom f)

@[simp] theorem hom_id (A : AbelianScheme S) : hom (𝟙 A) = 𝟙 A.X.left := rfl

@[simp] theorem hom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    hom (f ≫ g) = hom f ≫ hom g := rfl

/-- The group-valued functor of points of an abelian scheme. -/
abbrev points (A : AbelianScheme S) := GroupScheme.points A.toGrp

/-- The ring of endomorphisms, with multiplication given by composition. -/
abbrev End (A : AbelianScheme S) := CategoryTheory.End A

instance (A : AbelianScheme S) : Ring (End A) :=
  inferInstanceAs (Ring (CategoryTheory.End A))

/-- The bundle satisfies the source's geometric conditions. -/
theorem isAbelian (A : AbelianScheme S) : GroupScheme.IsAbelian A.toGrp :=
  ⟨A.smooth, A.proper, A.geometricallyConnected⟩

/-- Base change is the actual scheme pullback, with its induced operations. -/
def baseChange (f : T ⟶ S) : AbelianScheme S ⥤ AbelianScheme T where
  obj A := {
    (CommGroupScheme.baseChange f).obj A.toCommGroupScheme with
    smooth := by change Smooth (Limits.pullback.snd A.X.hom f); infer_instance
    proper := by change IsProper (Limits.pullback.snd A.X.hom f); infer_instance
    geometricallyConnected := by
      change GeometricallyConnected (Limits.pullback.snd A.X.hom f)
      infer_instance }
  map g := (CommGroupScheme.baseChange f).map (commHom g)
  map_id A := (CommGroupScheme.baseChange f).map_id A.toCommGroupScheme
  map_comp g h := (CommGroupScheme.baseChange f).map_comp (commHom g) (commHom h)

/-- A fixed relative dimension is an additional property, not a chosen global number. -/
abbrev HasRelativeDimension (A : AbelianScheme S) (g : ℕ) : Prop :=
  SmoothOfRelativeDimension g A.X.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- A specified constant relative dimension is preserved by arbitrary base change. -/
theorem hasRelativeDimension_baseChange (A : AbelianScheme S) (g : ℕ)
    (h : A.HasRelativeDimension g) (f : T ⟶ S) :
    ((baseChange f).obj A).HasRelativeDimension g := by
  change SmoothOfRelativeDimension g (Limits.pullback.snd A.X.hom f)
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension g) A.X.hom f h

end AbelianScheme
end Langlands
