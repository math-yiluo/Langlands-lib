/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# The explicit derived comparison with an injective resolution

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]

/-- Compare with the chosen resolution, commute the termwise functor past extension
by zero, and then apply a lift of the identity to the specified resolution.

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison). -/
noncomputable def injectiveResolutionDerivedComparison
    (v : A ⥤ B) [v.Additive] {X : A} (I : InjectiveResolution X) :
    (v.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) ⟶
      DerivedCategory.Q.obj
        (((v.mapHomologicalComplex _).obj I.cocomplex).extend
          ComplexShape.embeddingUpNat) :=
  DerivedCategory.Plus.ι.map (v.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).hom ≫
    DerivedCategory.Q.map
      ((injectiveResolution X).cocomplex.mapExtendIso ComplexShape.embeddingUpNat v).hom ≫
    DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((v.mapHomologicalComplex _).map
        (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X)))
      ComplexShape.embeddingUpNat)

set_option backward.isDefEq.respectTransparency false in
/-- The explicit derived comparison induces the usual injective-resolution
identification on homology.

Source: Stacks Project, Derived Categories, Tags 05TE and 015B.
(blueprint: lem-sc-p1-injective-resolution-derived-comparison).

Proof: Expand the chosen-resolution single-object identification. Naturality of
localization homology moves the two localized chain maps through its homology
isomorphism. Naturality of extension homology moves the lifted identity through
extension by zero. The map/extension isomorphism cancels with its inverse in
`isoRightDerivedObjCochainComplex`. The homology factorization through the homotopy
category cancels too. Finally naturality of `isoRightDerivedObj` for the lift of
`id_X` identifies the result with the prescribed resolution's identification.
-/
theorem injectiveResolutionDerivedComparison_homology
    (v : A ⥤ B) [v.Additive] {X : A} (I : InjectiveResolution X) (n : ℕ) :
    (DerivedCategory.homologyFunctor B (n : ℤ)).map
        (injectiveResolutionDerivedComparison v I) ≫
      ((DerivedCategory.homologyFunctorFactors B (n : ℤ)).app _ ≪≫
        ((v.mapHomologicalComplex _).obj I.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom =
    (v.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n).hom ≫
      (I.isoRightDerivedObj v n).hom := by
  simp only [injectiveResolutionDerivedComparison, Functor.map_comp, Category.assoc,
    Iso.trans_hom]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    HomologicalComplex.extendHomologyIso_hom_naturality]
  simp only [Functor.homologyRightDerivedFunctorPlusObjSingleFunctorIso,
    DerivedCategory.Plus.homologyFunctorObjQIso,
    InjectiveResolution.isoRightDerivedObjCochainComplex, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.symm_inv, Category.assoc]
  have h := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 X)
    (injectiveResolution X) I (InjectiveResolution.desc (𝟙 X) I (injectiveResolution X))
    (InjectiveResolution.desc_commutes_zero _ _ _) v n
  simp only [Functor.map_id, Category.id_comp, Functor.comp_map,
    HomologicalComplex.homologyFunctor_map] at h
  rw [h]
  simp only [Iso.inv_hom_id_assoc]
  rfl

end CategoryTheory
