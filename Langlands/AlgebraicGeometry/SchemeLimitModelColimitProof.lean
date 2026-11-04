import Langlands.AlgebraicGeometry.SchemeLimitModelColimitStatement
import Langlands.AlgebraicGeometry.SchemeLimitModelProof
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered

/-! # The relative model Hom colimit comparison -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- Morphism factorization and eventual equality identify the actual Hom colimit
with morphisms over the limit and give the cocone universal property. -/
theorem modelHomColimitComparison : ModelHomColimitComparison.{u} := by
  intro I _ _ D _ S X Y t a b c hc p hp
  obtain ⟨hfac, heq, _⟩ := modelMorphismDescent I D S X Y t a b c hc p hp
  have hinj : QuasiCompact a → LocallyOfFiniteType b →
      Function.Injective (homColimitMap D t a b c p hp) := by
    intro hqc hft
    apply (homCoconeTypes D t a b c p hp).descColimitType_injective_iff_of_isFiltered.mpr
    intro i j fi fj hij
    obtain ⟨k, r, s, hrs⟩ := heq hqc hft i.unop j.unop fi fj hij
    exact ⟨op k, r.op, s.op, hrs⟩
  have hsurj : QuasiCompact a → QuasiSeparated a → LocallyOfFinitePresentation b →
      Function.Surjective (homColimitMap D t a b c p hp) := by
    intro hqc hqs hfp f
    obtain ⟨i, fi, hfi⟩ := hfac hqc hqs hfp f
    exact ⟨homColimitι D t a b i fi, hfi⟩
  refine ⟨hinj, hsurj, ?_⟩
  intro hqc hqs hfp
  let := hfp
  have hbij : Function.Bijective (homColimitMap D t a b c p hp) :=
    ⟨hinj hqc inferInstance, hsurj hqc hqs hfp⟩
  exact ⟨hbij, (homCoconeTypes D t a b c p hp).isColimit_iff.mp ⟨hbij⟩⟩

end Langlands.AlgebraicGeometry.SchemeLimitModel
