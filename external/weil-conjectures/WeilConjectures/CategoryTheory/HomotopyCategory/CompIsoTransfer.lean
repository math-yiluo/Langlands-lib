/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.HomEquivCompIso
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# `compIsoTransfer` on homotopy categories

For additive functors and adjunctions `T ⊣ R'`, `Ψ ⊣ R` with isomorphisms `τ : T ⋙ Φ ≅ Ψ`,
`τ' : T' ⋙ Φ ≅ Ψ'`, the map `CategoryTheory.Adjunction.compIsoTransfer` of the induced data on
the homotopy categories is, on the image of a complex `Y`, the image of the map of complexes
given degreewise by `compIsoTransfer` of the original data
(`CategoryTheory.Adjunction.compIsoTransfer_mapHomotopyCategory_quotient`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C C' D E : Type*} [Category C] [Category C'] [Category D] [Category E]
  [Preadditive C] [Preadditive C'] [Preadditive D] [Preadditive E]
  {T : C ⥤ D} {T' : C' ⥤ D} {Φ : D ⥤ E} {Ψ : C ⥤ E} {Ψ' : C' ⥤ E} {R' : D ⥤ C} {R : E ⥤ C}
  [T.Additive] [T'.Additive] [Φ.Additive] [Ψ.Additive] [Ψ'.Additive] [R'.Additive] [R.Additive]
  {ι : Type*} (c : ComplexShape ι)
  [(HomotopyCategory.quotient C c).IsLocalization (HomologicalComplex.homotopyEquivalences C c)]
  [(HomotopyCategory.quotient D c).IsLocalization (HomologicalComplex.homotopyEquivalences D c)]
  [(HomotopyCategory.quotient E c).IsLocalization (HomologicalComplex.homotopyEquivalences E c)]

/-- `compIsoTransfer` of the data induced on the homotopy categories is, on the image of a
complex `Y`, the image of the map of complexes given degreewise by `compIsoTransfer`. -/
lemma compIsoTransfer_mapHomotopyCategory_quotient (adj' : T ⊣ R') (adj : Ψ ⊣ R)
    (τ : T ⋙ Φ ≅ Ψ) (τ' : T' ⋙ Φ ≅ Ψ') (Y : HomologicalComplex C' c)
    (φ : (R'.mapHomologicalComplex c).obj ((T'.mapHomologicalComplex c).obj Y) ⟶
      (R.mapHomologicalComplex c).obj ((Ψ'.mapHomologicalComplex c).obj Y))
    (hφ : ∀ n, φ.f n = compIsoTransfer adj' adj τ τ' (Y.X n)) :
    compIsoTransfer (adj'.mapHomotopyCategory c) (adj.mapHomotopyCategory c)
        (Functor.mapHomotopyCategoryCompIso τ c) (Functor.mapHomotopyCategoryCompIso τ' c)
        ((HomotopyCategory.quotient C' c).obj Y) = (HomotopyCategory.quotient C c).map φ := by
  refine Eq.trans (b := (HomotopyCategory.quotient C c).map
    ((adj.mapHomologicalComplex c).unit.app _ ≫ (R.mapHomologicalComplex c).map
      ((Functor.mapHomologicalComplexCompIso τ c).inv.app _ ≫
        (Φ.mapHomologicalComplex c).map ((adj'.mapHomologicalComplex c).counit.app _) ≫
        (Functor.mapHomologicalComplexCompIso τ' c).hom.app Y))) ?_ ?_
  · rw [compIsoTransfer, homEquiv_unit]
    erw [mapHomotopyCategory_unit_app_quotient, mapHomotopyCategory_counit_app_quotient]
    rfl
  · congr 1
    ext n
    simp only [hφ, compIsoTransfer, homEquiv_unit]
    simp

end CategoryTheory.Adjunction
