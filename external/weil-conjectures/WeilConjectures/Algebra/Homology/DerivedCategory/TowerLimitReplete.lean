/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLimitEpimorphicTower

/-!
# Derived limits of towers of epimorphisms in a replete abelian category

Let `C` be an abelian category in which, for every tower of epimorphisms `⋯ ⟶ X₁ ⟶ X₀`, the
projection `lim Xₙ ⟶ X₀` is an epimorphism (`CategoryTheory.EpiπAppZeroOfEpi`), for instance
sheaves on a replete topos such as the pro-étale site (Bhatt–Scholze, *The pro-étale topology for
schemes*, §3.1). Then `lim¹` of a tower of epimorphisms vanishes
(`CategoryTheory.epi_one_sub_of_epiπAppZeroOfEpi`), so that, if moreover countable
products are exact, the limit of a tower of epimorphisms is its derived limit:

- `DerivedCategory.isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi`: for towers of complexes with
  degreewise epimorphic transitions, generalising
  `AlgebraicGeometry.ProEtale.isHomotopyLimit_mapCone_Q_of_epi` from sheaves of modules on the
  pro-étale site;
- `DerivedCategory.isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi`: for towers of
  objects placed in degree `0`.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

namespace DerivedCategory

open Pretriangulated

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [Abelian.HasKInjectiveResolutions C]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]
  [HasLimitsOfShape ℕᵒᵖ C]

/-- **Derived limits of towers of epimorphisms in a replete abelian category**: in an abelian
category with exact countable products in which sequential limits of epimorphisms project
epimorphically onto the first term, the image in the derived category of a limit cone `c` of a
tower `T` of complexes whose transitions are degreewise epimorphisms is a homotopy limit cone:
in each degree `1 - t` is an epimorphism on `∏ Tₙ`
(`CategoryTheory.epi_one_sub_of_epiπAppZeroOfEpi`), so that
`DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi_one_sub` applies. -/
theorem isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi (hC : EpiπAppZeroOfEpi C)
    {T : ℕᵒᵖ ⥤ CochainComplex C ℤ}
    (hT : ∀ (n : ℕ) (i : ℤ), Epi ((T.map (homOfLE n.le_succ).op).f i)) {c : Cone T}
    (hc : IsLimit c) :
    IsHomotopyLimit (Q.mapCone c) :=
  isHomotopyLimit_mapCone_Q_of_epi_one_sub (fun i _ hP t ht ↦
    epi_one_sub_of_epiπAppZeroOfEpi hC (F := T ⋙ HomologicalComplex.eval _ _ i)
      (fun n ↦ hT n i) hP t ht) hc

/-- **Derived limits of towers of epimorphisms in a replete abelian category**, for objects
placed in degree `0`: for a tower `F` with epimorphic transitions and a limit cone `c`, the
image of `c` in the derived category is a homotopy limit cone, that is
`lim Fₙ ≅ R lim Fₙ`. -/
theorem isHomotopyLimit_mapCone_singleFunctor_of_epiπAppZeroOfEpi (hC : EpiπAppZeroOfEpi C)
    {F : ℕᵒᵖ ⥤ C} (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) {c : Cone F}
    (hc : IsLimit c) :
    IsHomotopyLimit ((singleFunctor C 0).mapCone c) := by
  have h := isHomotopyLimit_mapCone_Q_of_epiπAppZeroOfEpi hC
    (T := F ⋙ HomologicalComplex.single C (ComplexShape.up ℤ) 0) (fun n i ↦ ?_)
    (isLimitOfPreserves (HomologicalComplex.single C (ComplexShape.up ℤ) 0) hc)
  · refine IsHomotopyLimit.of_iso (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (singleFunctorIsoCompQ C 0).symm) h _
      ((singleFunctorIsoCompQ C 0).symm.app c.pt) fun n ↦ ?_
    simp only [Functor.comp_obj, Functor.mapCone_pt, Functor.mapCone_π_app, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.id_comp, Iso.app_hom]
    exact ((singleFunctorIsoCompQ C 0).inv.naturality (c.π.app (op n)))
  · by_cases hi : i = 0
    · subst hi
      rw [Functor.comp_map, HomologicalComplex.single_map_f_self]
      have := hF n
      infer_instance
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).epi _

end DerivedCategory
