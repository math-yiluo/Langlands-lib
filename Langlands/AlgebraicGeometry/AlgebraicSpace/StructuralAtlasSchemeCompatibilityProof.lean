import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasSchemeCompatibilityStatement
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationSourceDescent
import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentProof

/-! # Structural atlas geometry agrees with scheme geometry on actual schemes

The identity atlas gives each implication from the scheme property of `U.hom` to the atlas
predicate. Conversely, an actual etale surjective atlas of the represented scheme `U` is the
Yoneda image of an etale surjective scheme morphism `f : W ⟶ U` over `S`, and the property of
the atlas structure map `W.hom = f.left ≫ U.hom` descends to `U.hom` along `f.left`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- An actual etale surjective atlas of a represented scheme is the Yoneda image of a morphism
over `S` whose underlying scheme morphism is etale and surjective. -/
theorem exists_etale_surjective_of_represented_atlas {W U : Over S}
    (a : (schemeYoneda S).obj W ⟶ (schemeYoneda S).obj U)
    (ha : IsEtale a) (hs : IsSurjective a) :
    ∃ f : W ⟶ U, Etale f.left ∧ Surjective f.left := by
  obtain ⟨f, rfl⟩ := (schemeYoneda S).map_surjective a
  exact ⟨f,
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)) ha,
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)) hs⟩

/-- Structural smoothness of an actual scheme is smoothness of its structure morphism. -/
theorem smoothOverBase_schemeToSpace_iff (U : Over S) :
    SmoothOverBase ((schemeToSpace S).obj U) ↔ Smooth U.hom := by
  refine ⟨fun h => ?_, SmoothOverBase.of_scheme U⟩
  obtain ⟨W, a, ha, hs, hW⟩ := h.exists_atlas
  obtain ⟨f, hfE, hfS⟩ := exists_etale_surjective_of_represented_atlas a ha hs
  exact smoothEtaleSourceDescent _ _ _ f.left U.hom hfE hfS (by rw [Over.w f]; exact hW)

/-- Structural local finite presentation of an actual scheme is local finite presentation of
its structure morphism. -/
theorem locallyOfFinitePresentationOverBase_schemeToSpace_iff (U : Over S) :
    LocallyOfFinitePresentationOverBase ((schemeToSpace S).obj U) ↔
      LocallyOfFinitePresentation U.hom := by
  refine ⟨fun h => ?_, LocallyOfFinitePresentationOverBase.of_scheme U⟩
  obtain ⟨W, a, ha, hs, hW⟩ := h.exists_atlas
  obtain ⟨f, hfE, hfS⟩ := exists_etale_surjective_of_represented_atlas a ha hs
  have : LocallyOfFinitePresentation (f.left ≫ U.hom) := by rw [Over.w f]; exact hW
  exact locallyOfFinitePresentation_of_surjective_flat_comp f.left U.hom

/-- Structural local finite type of an actual scheme is local finite type of its structure
morphism. -/
theorem locallyOfFiniteTypeOverBase_schemeToSpace_iff (U : Over S) :
    LocallyOfFiniteTypeOverBase ((schemeToSpace S).obj U) ↔ LocallyOfFiniteType U.hom := by
  refine ⟨fun h => ?_, LocallyOfFiniteTypeOverBase.of_scheme U⟩
  obtain ⟨W, a, ha, hs, hW⟩ := h.exists_atlas
  obtain ⟨f, hfE, hfS⟩ := exists_etale_surjective_of_represented_atlas a ha hs
  exact locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp _ _ _ f.left
    U.hom hfS inferInstance inferInstance (by rw [Over.w f]; exact hW)

/-- The three structural atlas predicates agree with the Mathlib scheme properties on every
actual scheme over every scheme base. -/
theorem structuralAtlasSchemeCompatibility :
    StructuralAtlasSchemeCompatibilityStatement.{u} := fun _ U =>
  ⟨smoothOverBase_schemeToSpace_iff U, locallyOfFinitePresentationOverBase_schemeToSpace_iff U,
    locallyOfFiniteTypeOverBase_schemeToSpace_iff U⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
