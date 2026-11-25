/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndSurjective

/-!
# Endomorphisms of the regular module and monoidal functors

For a commutative algebra object `R` of a braided preadditive monoidal category, the ring
homomorphism `Γ R →+* End (Mod.regular R)` sending a global section to the multiplication by it
is bijective (`CategoryTheory.Mod.regularEndRingHom_bijective`).

A lax monoidal functor `F` sends the regular module `R` to the regular module `F R`, and the
multiplication by a global section `s` to the multiplication by its image `ε ≫ F s`
(`CategoryTheory.Functor.mapMod_map_regularEndRingHom`). Consequently, when `F` is fully faithful
on module objects, the map `Γ R →+* Γ (F R) →+* End (Mod.regular (F R))` is bijective
(`CategoryTheory.Functor.bijective_regularEndRingHom_comp_mapFunctor`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- The multiplication by global sections is injective: a global section `s` is recovered from
the multiplication by `s` as `η ≫ s·`. -/
lemma regularEndRingHom_injective : Function.Injective (regularEndRingHom (R := R)) := by
  intro s t h
  ext1
  rw [← one_comp_regularLift_regular s.hom, ← one_comp_regularLift_regular t.hom]
  exact congrArg (fun φ : End (regular R) ↦ η[R] ≫ φ.asHom.hom) h

/-- The endomorphisms of the regular module `R` are the multiplications by the global sections
of `R`. -/
lemma regularEndRingHom_bijective : Function.Bijective (regularEndRingHom (R := R)) :=
  ⟨regularEndRingHom_injective, regularEndRingHom_surjective⟩

end CategoryTheory.Mod

namespace CategoryTheory.Functor

open LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [BraidedCategory C] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  [Preadditive D] [MonoidalPreadditive D] [BraidedCategory D] (F : C ⥤ D) [F.LaxBraided]
  [F.Additive] (R : C) [MonObj R] [IsCommMonObj R]

/-- A lax monoidal functor sends the multiplication by a global section `s` on the regular module
`R` to the multiplication by `ε ≫ F s` on the regular module `F R`. -/
lemma mapMod_map_regularEndRingHom (s : Γ R) :
    (F.mapMod R).map ((Mod.regularEndRingHom s)).asHom =
      (Mod.regularEndRingHom (Γ.mapFunctor F s)).asHom := by
  refine Mod.regular_hom_ext ?_
  change η[F.obj R] ≫ F.map (Mod.regularLift (Mod.regular R) s.hom).hom =
    η[F.obj R] ≫ (Mod.regularLift (Mod.regular (F.obj R)) (Γ.mapFunctor F s).hom).hom
  rw [Mod.one_comp_regularLift_regular, Γ.mapFunctor_hom]
  change (ε F ≫ F.map η[R]) ≫ F.map (Mod.regularLift (Mod.regular R) s.hom).hom = _
  rw [Category.assoc, ← F.map_comp, Mod.one_comp_regularLift_regular]

/-- If `F` is fully faithful on module objects, the composite
`Γ R →+* Γ (F R) →+* End (Mod.regular (F R))` is bijective. -/
lemma bijective_regularEndRingHom_comp_mapFunctor (hF : (F.mapMod R).FullyFaithful) :
    Function.Bijective (Mod.regularEndRingHom.comp (Γ.mapFunctor F (R := R))) := by
  have h : ⇑(Mod.regularEndRingHom.comp (Γ.mapFunctor F (R := R))) =
      (F.mapMod R).mapEnd (Mod.regular R) ∘ Mod.regularEndRingHom := by
    ext1 s
    exact End.ext (mapMod_map_regularEndRingHom F R s).symm
  rw [h]
  exact (hF.mulEquivEnd _).bijective.comp Mod.regularEndRingHom_bijective

end CategoryTheory.Functor
