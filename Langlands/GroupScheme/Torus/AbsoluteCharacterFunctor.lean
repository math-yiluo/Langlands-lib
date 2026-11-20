import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteFunctor
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting
import Langlands.GroupScheme.Torus.SplittingDescentHelpers
import Langlands.GroupScheme.Torus.SurjectionIsogenySectionProof

/-! # The absolute-Galois character functor of field tori -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.GroupScheme

variable (k : Type u) [Field k]

/-- The geometric torus property on actual commutative group schemes over a field. -/
def fieldTorusProperty : ObjectProperty (CommGroupScheme (Spec (CommRingCat.of k))) :=
  fun T => IsTorus T.toGrp

/-- Actual field tori and all their ground-field group-scheme homomorphisms. -/
abbrev FieldTorus := (fieldTorusProperty k).FullSubcategory

/-- Freeness of the underlying integral module of a finitely generated discrete
absolute-Galois module. -/
def freeDiscreteGaloisModuleProperty :
    ObjectProperty (FGDiscreteGaloisModule.{u, v} k) :=
  fun A => Module.Free ℤ A

/-- Finite free integral modules with continuous discrete absolute-Galois action. -/
abbrev FreeDiscreteGaloisModule :=
  (freeDiscreteGaloisModuleProperty.{u, v} k).FullSubcategory

namespace FieldTorus

/-- Regard a field torus as a group of multiplicative type. -/
abbrev toMultiplicativeTypeGroup : FieldTorus k ⥤ MultiplicativeTypeGroup k :=
  (fieldTorusProperty k).ιOfLE (fun _ hT => IsTorus.isMultiplicativeType hT)

/-- The same actual character functor, restricted to tori and finite free modules. -/
def characterFunctor : (FieldTorus k)ᵒᵖ ⥤ FreeDiscreteGaloisModule.{u, u} k :=
  (freeDiscreteGaloisModuleProperty k).lift
    ((toMultiplicativeTypeGroup k).op ⋙ MultiplicativeTypeGroup.characterFunctor k)
    (fun T => by
      change Module.Free ℤ (characterLattice
        ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T.unop.obj))
      have hT := IsTorus.baseChange_of_isAlgebraic k (SeparableClosure k)
        T.unop.obj.toGrp T.unop.property
      exact (TorusSurjectionIsogenySection.characterLattice_free_finite
        ((toriAreSplit_of_isSepClosed (SeparableClosure k)) _ hT)).1)

/-- The composite with the lattice inclusion recovers the ambient character functor on tori. -/
theorem characterFunctor_forget :
    characterFunctor k ⋙ (freeDiscreteGaloisModuleProperty k).ι =
      (toMultiplicativeTypeGroup k).op ⋙ MultiplicativeTypeGroup.characterFunctor k := rfl

end FieldTorus

end Langlands.GroupScheme
