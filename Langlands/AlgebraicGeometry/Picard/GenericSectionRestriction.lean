import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Restriction of actual sections to an integral base's generic point -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

variable {S X : Scheme.{u}} [IsIntegral S] (p : X ⟶ S)

/-- Restrict an actual section along the canonical generic residue-field map. -/
def genericSectionRestriction :
    {s : S ⟶ X // s ≫ p = 𝟙 S} →
      {sη : Spec (S.residueField (genericPoint S)) ⟶ X //
        sη ≫ p = S.fromSpecResidueField (genericPoint S)} :=
  fun s => ⟨S.fromSpecResidueField (genericPoint S) ≫ s.val, by
    rw [Category.assoc, s.property, Category.comp_id]⟩

/-- Maps over the same separated target agree if their actual generic
residue-field restrictions agree. -/
theorem hom_ext_of_genericPoint [IsSeparated p] {f g : S ⟶ X}
    (hbase : f ≫ p = g ≫ p)
    (hη : S.fromSpecResidueField (genericPoint S) ≫ f =
      S.fromSpecResidueField (genericPoint S) ≫ g) : f = g := by
  apply ext_of_fromSpecResidueField_eq f g p {genericPoint S}
    (dense_iff_closure_eq.mpr (genericPoint_closure S)) ?_ hbase
  intro x hx
  have hx' : x = genericPoint S := Set.mem_singleton_iff.mp hx
  subst x
  exact hη

/-- A section of a separated morphism over an integral base is determined
by its restriction to the generic point. -/
theorem genericSectionRestriction_injective [IsSeparated p] :
    Function.Injective (genericSectionRestriction p) := by
  intro s t h
  apply Subtype.ext
  apply hom_ext_of_genericPoint p (s.property.trans t.property.symm)
  exact congrArg Subtype.val h

end Langlands.AlgebraicGeometry
