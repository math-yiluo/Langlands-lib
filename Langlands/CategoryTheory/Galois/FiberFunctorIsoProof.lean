import Langlands.CategoryTheory.Galois.FiberFunctorIsoStatement
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!
# Isomorphisms between fibre functors

Construct comparison maps from the pointed Galois-object colimit presentation
and nonempty sections of finite cofiltered systems, then use invertibility of
endomorphisms of fibre functors.
-/

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace Langlands.CategoryTheory.Galois

variable {C : Type v} [Category.{u} C] [GaloisCategory C]
  (F G : C ⥤ FintypeCat.{u})
  [FiberFunctor F] [FiberFunctor G]

/-- A coherent family of points on pointed Galois objects gives a comparison map. -/
private theorem nonempty_fiberFunctor_hom : Nonempty (F ⟶ G) := by
  let H : PointedGaloisObject F ⥤ Type u :=
    PointedGaloisObject.incl F ⋙ G ⋙ FintypeCat.incl
  have : ∀ A : PointedGaloisObject F, Finite (H.obj A) :=
    fun A => inferInstanceAs (Finite (G.obj A.obj))
  have : ∀ A : PointedGaloisObject F, Nonempty (H.obj A) :=
    fun A => nonempty_fiber_of_isConnected G A.obj
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system H
  change (A : PointedGaloisObject F) → G.obj A.obj at s
  change ∀ ⦃A B : PointedGaloisObject F⦄ (f : A ⟶ B), G.map f.val (s A) = s B at hs
  let c : Cocone ((PointedGaloisObject.incl F).op ⋙ coyoneda) :=
    { pt := G ⋙ FintypeCat.incl
      ι :=
        { app := fun A =>
            { app := fun X => ↾fun f => G.map f (s A.unop)
              naturality := fun X Y f => by
                ext (g : A.unop.obj ⟶ X)
                change G.map (g ≫ f) (s A.unop) = G.map f (G.map g (s A.unop))
                simp only [G.map_comp, FintypeCat.comp_apply] }
          naturality := fun A B f => by
            ext X (g : A.unop.obj ⟶ X)
            change G.map (f.unop.val ≫ g) (s B.unop) = G.map g (s A.unop)
            rw [G.map_comp, FintypeCat.comp_apply]
            exact congrArg (G.map g) (hs f.unop) } }
  let α : F ⋙ FintypeCat.incl ⟶ G ⋙ FintypeCat.incl :=
    (PointedGaloisObject.isColimit F).desc c
  exact ⟨((Functor.FullyFaithful.ofFullyFaithful FintypeCat.incl).whiskeringRight C).preimage α⟩

/-- Two fibre functors on a Galois category admit a natural isomorphism. -/
theorem fiberFunctorIsoExists : FiberFunctorIsoExists F G := by
  obtain ⟨f⟩ := nonempty_fiberFunctor_hom F G
  obtain ⟨g⟩ := nonempty_fiberFunctor_hom G F
  have : IsIso (f ≫ g) := FibreFunctor.end_isIso F (f ≫ g)
  have : IsIso (g ≫ f) := FibreFunctor.end_isIso G (g ≫ f)
  have : Mono f := mono_of_mono f g
  have : IsSplitEpi f :=
    IsSplitEpi.mk'
      { section_ := inv (g ≫ f) ≫ g
        id := by simp [Category.assoc] }
  have : IsIso f := isIso_of_mono_of_isSplitEpi f
  exact ⟨asIso f⟩

end Langlands.CategoryTheory.Galois
