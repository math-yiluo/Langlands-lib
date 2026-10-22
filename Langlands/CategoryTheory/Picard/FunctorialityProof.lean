import Langlands.CategoryTheory.Picard.FunctorialityStatements

/-!
# Functoriality of the categorical Picard group

The induced additive homomorphisms respect identities and composition and are
invariant under ordinary natural isomorphisms. Each equality is checked on
underlying skeleton classes of chosen representatives.
-/

open CategoryTheory

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace Langlands.CategoryTheory.PicardGroup

/-- The identity strong monoidal functor induces the identity Picard homomorphism. -/
theorem mapIdentity
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C] :
    MapIdentityStatement C := by
  refine AddMonoidHom.ext fun x => ext ?_
  rw [toSkeletonClass_map, AddMonoidHom.id_apply, ← toSkeleton_representative x,
    Functor.mapSkeleton_obj_toSkeleton, Functor.id_obj]

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Composition of strong monoidal functors induces composition of Picard homomorphisms. -/
theorem mapComposition [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    MapCompositionStatement F G := by
  refine AddMonoidHom.ext fun x => ext ?_
  rw [AddMonoidHom.comp_apply, toSkeletonClass_map, toSkeletonClass_map, toSkeletonClass_map,
    ← toSkeleton_representative x, Functor.mapSkeleton_obj_toSkeleton,
    Functor.mapSkeleton_obj_toSkeleton, Functor.mapSkeleton_obj_toSkeleton, Functor.comp_obj]

/-- An ordinary natural isomorphism suffices for equality of Picard homomorphisms. -/
theorem mapIso [BraidedCategory C] [BraidedCategory D]
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] :
    MapIsoStatement F G := by
  intro e
  refine AddMonoidHom.ext fun x => ext ?_
  rw [toSkeletonClass_map, toSkeletonClass_map, ← toSkeleton_representative x,
    Functor.mapSkeleton_obj_toSkeleton, Functor.mapSkeleton_obj_toSkeleton]
  exact congr_toSkeleton_of_iso (e.app (representative x))

end Langlands.CategoryTheory.PicardGroup
