import Mathlib.CategoryTheory.Galois.Basic

/-!
# Existence of an isomorphism between fibre functors

The statement corresponding to SGA 1, Exposé V, Corollary 5.7,
using Mathlib's Galois-category and fibre-functor classes.
-/

universe v u

open CategoryTheory

namespace Langlands.CategoryTheory.Galois

/-- Two fibre functors on a Galois category admit a natural isomorphism. -/
def FiberFunctorIsoExists {C : Type v} [Category.{u} C] [GaloisCategory C]
    (F G : C ⥤ FintypeCat.{u})
    [PreGaloisCategory.FiberFunctor F] [PreGaloisCategory.FiberFunctor G] : Prop :=
  Nonempty (F ≅ G)

end Langlands.CategoryTheory.Galois
