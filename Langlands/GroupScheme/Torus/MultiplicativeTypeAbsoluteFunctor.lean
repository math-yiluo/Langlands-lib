import Langlands.GroupScheme.Torus.DiscreteGaloisModule
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteCharacterFiniteProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteCharacterSmoothProof

/-! # The actual absolute-Galois character functor -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable (k : Type u) [Field k]

/-- The unchanged multiplicative-type predicate on actual commutative group schemes. -/
def multiplicativeTypeProperty :
    ObjectProperty (CommGroupScheme (Spec (CommRingCat.of k))) :=
  fun T => IsMultiplicativeType T.toGrp

/-- Actual multiplicative-type group schemes with every ground-field homomorphism. -/
abbrev MultiplicativeTypeGroup := (multiplicativeTypeProperty k).FullSubcategory

namespace MultiplicativeTypeGroup

/-- Forget the multiplicative-type property, retaining the actual groups and maps. -/
abbrev inclusion :
    MultiplicativeTypeGroup k ⥤ CommGroupScheme (Spec (CommRingCat.of k)) :=
  (multiplicativeTypeProperty k).ι

/-- The existing actual character functor, with proved open character stabilizers. -/
def smoothCharacterFunctor :
    (MultiplicativeTypeGroup k)ᵒᵖ ⥤
      SmoothRep.{0, u, u} ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k) :=
  (smoothRepProperty ℤ (SeparableClosure k ≃ₐ[k] SeparableClosure k)).lift
    ((inclusion k).op ⋙ characterLattice.galoisFunctor k (SeparableClosure k))
    (fun T => multiplicativeTypeAbsoluteCharacterSmooth k T.unop.obj T.unop.property)

/-- Actual separable-closure characters as finitely generated discrete Galois modules. -/
def characterFunctor :
    (MultiplicativeTypeGroup k)ᵒᵖ ⥤ FGDiscreteGaloisModule.{u, u} k :=
  (fgDiscreteGaloisModuleProperty k).lift (smoothCharacterFunctor k)
    (fun T => multiplicativeTypeAbsoluteCharacterFinite k T.unop.obj T.unop.property)

/-- The representation is exactly the published canonical character action. -/
theorem characterFunctor_representation (T : MultiplicativeTypeGroup k) :
    ((characterFunctor k).obj (op T)).representation =
      characterLattice.galoisRepresentation k (SeparableClosure k) T.obj := rfl

/-- Morphisms are the actual pullbacks of characters after scalar extension. -/
@[simp]
theorem characterFunctor_map_apply
    {H G : (MultiplicativeTypeGroup k)ᵒᵖ} (f : H ⟶ G)
    (χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj H.unop.obj)) :
    FGDiscreteGaloisModule.hom ((characterFunctor k).map f) χ =
      (CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).map
        f.unop.hom ≫ χ := rfl

/-- Forgetting the two proved properties recovers the published character functor. -/
theorem characterFunctor_forget :
    characterFunctor k ⋙ FGDiscreteGaloisModule.toRep =
      (inclusion k).op ⋙ characterLattice.galoisFunctor k (SeparableClosure k) := rfl

end MultiplicativeTypeGroup

end Langlands.GroupScheme
