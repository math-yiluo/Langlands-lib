/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Homology of single complexes and functors preserving homology

For a functor `F` which preserves homology, the isomorphism `H_j(F(K)) ≅ F(H_j(K))`
(`Functor.mapHomologicalComplexHomologyIso`) is compatible with the computation
`H_j(A[j]) ≅ A` of the homology of single complexes.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace ShortComplex

variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology] (S : ShortComplex C)

@[reassoc (attr := simp)]
lemma homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  rw [S.leftHomologyData.mapHomologyIso_eq F, S.leftHomologyData.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc, Category.assoc]
  congr 1
  erw [← F.map_comp, LeftHomologyData.π_comp_homologyIso_inv]
  exact F.map_comp _ _

end ShortComplex

namespace Functor

variable (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι)
  (j : ι) [DecidableEq ι]

set_option linter.flexible false in
/-- The isomorphism `H_j(F(A[j])) ≅ F(H_j(A[j]))` is compatible with the identifications
`H_j(A[j]) ≅ A` and `F(A[j]) ≅ F(A)[j]`. -/
lemma mapHomologicalComplexHomologyIso_hom_app_single (A : C) :
    (F.mapHomologicalComplexHomologyIso c j).hom.app ((HomologicalComplex.single C c j).obj A) ≫
        F.map ((HomologicalComplex.homologyFunctorSingleIso C c j).hom.app A) =
      HomologicalComplex.homologyMap
          ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A) j ≫
        (HomologicalComplex.homologyFunctorSingleIso D c j).hom.app (F.obj A) := by
  have hμ : (F.mapHomologicalComplexHomologyIso c j).hom.app
      ((HomologicalComplex.single C c j).obj A) =
      ((((HomologicalComplex.single C c j).obj A).sc j).mapHomologyIso F).hom := by
    simp [mapHomologicalComplexHomologyIso, mapHomologicalComplexCompShortComplexFunctorIso,
      ShortComplex.homologyFunctorIso]
    erw [Category.id_comp, Category.id_comp, Functor.map_id, Category.comp_id]
  rw [hμ, ← cancel_epi (((HomologicalComplex.single C c j).obj A).sc j |>.map F).homologyπ]
  have h₁ := ShortComplex.homologyπ_mapHomologyIso_hom F
    (((HomologicalComplex.single C c j).obj A).sc j)
  have h₂ := HomologicalComplex.homologyπ_naturality
    ((HomologicalComplex.singleMapHomologicalComplex F c j).hom.app A) j
  have h₃ := ShortComplex.mapCyclesIso_hom_iCycles
    (((HomologicalComplex.single C c j).obj A).sc j) F
  erw [reassoc_of% h₁, reassoc_of% h₂]
  simp only [HomologicalComplex.homologyFunctorSingleIso_hom_app]
  erw [← F.map_comp, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.singleObjCyclesSelfIso_hom,
    F.map_comp, reassoc_of% h₃, HomologicalComplex.cyclesMap_i_assoc]
  congr 1
  simp [HomologicalComplex.singleMapHomologicalComplex, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq, eqToHom_map]

end Functor

namespace NatTrans

/-- For a natural transformation `τ : Φ ⟶ Ψ` of additive functors and an object `F`, the map
induced by `τ` on `H⁰` of the single complex `F[0]` is, as an arrow, `τ.app F`. -/
noncomputable def homologyMapMapHomologicalComplexSingleArrowIso {Φ Ψ : C ⥤ D}
    [Φ.Additive] [Ψ.Additive] (τ : Φ ⟶ Ψ) (F : C) :
    Arrow.mk (HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ
      (ComplexShape.up ℤ)).app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj F)) 0) ≅
      Arrow.mk (τ.app F) := by
  have w : (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj F) ≫
        (HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) 0).hom.app F =
      (HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).hom.app F ≫
        (HomologicalComplex.single D (ComplexShape.up ℤ) 0).map (τ.app F) := by
    ext i
    by_cases hi : i = 0
    · subst hi
      simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
    · simp [HomologicalComplex.singleMapHomologicalComplex_hom_app_ne _ _ hi]
  refine Arrow.isoMk
    ((HomologicalComplex.homologyFunctor D _ 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app F) ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ _ _)
    ((HomologicalComplex.homologyFunctor D _ 0).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) 0).app F) ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ _ _) ?_
  simp only [Arrow.mk_left, Arrow.mk_right, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    HomologicalComplex.homologyFunctor_map, Arrow.mk_hom, Category.assoc,
    ← HomologicalComplex.singleObjHomologySelfIso_hom_naturality,
    ← HomologicalComplex.homologyMap_comp_assoc, w]

end NatTrans

end CategoryTheory
