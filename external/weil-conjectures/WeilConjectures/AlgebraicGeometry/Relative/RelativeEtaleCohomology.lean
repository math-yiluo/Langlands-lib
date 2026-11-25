/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.CategoryTheory.Abelian.Injective.Ext

/-!
# Relative étale cohomology in an injective-resolution model

## References

* Stacks Project, Cohomology on Sites, Tag 03AJ, relative refinement
* Stacks Project, Tag 03AJ, relative refinement
* Stacks Project, Tag 0G78, mapping-fibre functoriality
* Stacks Project, Tag 0G71, first arrow of the relative triangle
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Sections of a nonnegative sheaf complex, extended by zero in negative degrees. -/
noncomputable def relativeSections {T : Scheme.{u}} (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extend
    ComplexShape.embeddingUpNat

/-- Restriction from the terminal object, extended by zero in negative degrees. -/
noncomputable def relativeSectionRestriction (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSections (Scheme.Etale.mk (𝟙 T)) I ⟶ relativeSections U I :=
  HomologicalComplex.extendMap (etaleSectionMap
    ((MorphismProperty.Over.mkIdTerminal @Etale T).from U) I)
    ComplexShape.embeddingUpNat

/-- The actual mapping cone of restriction, shifted by minus one.
For an injective resolution and an open U this computes the relative derived sections. -/
noncomputable def relativeSectionComplex (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  (CochainComplex.mappingCone (relativeSectionRestriction T U I))⟦(-1 : ℤ)⟧

/-- Relative étale cohomology in a supplied injective-resolution model.
The resolution is a model, not an extra geometric assumption. -/
noncomputable def relativeCohomology (T : Scheme.{u}) (U : T.Etale)
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (I : InjectiveResolution G) (q : ℤ) : AddCommGrpCat.{u + 1} :=
  (relativeSectionComplex T U I.cocomplex).homology q

/-- The shifted cone map associated to a strictly commuting restriction square. -/
noncomputable def relativeFiberMap
    {A B A' B' : CochainComplex AddCommGrpCat.{u + 1} ℤ}
    (r : A ⟶ B) (r' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : a ≫ r' = r ≫ b) :
    (CochainComplex.mappingCone r)⟦(-1 : ℤ)⟧ ⟶
      (CochainComplex.mappingCone r')⟦(-1 : ℤ)⟧ :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom r r'
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (Arrow.homMk a b h))

/-- Projection from relative sections to absolute sections, with the ordinary cone sign. -/
noncomputable def relativeForgetComplex (T : Scheme.{u}) (U : T.Etale)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionComplex T U I ⟶ relativeSections (Scheme.Etale.mk (𝟙 T)) I :=
  (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map
      (CochainComplex.HomComplex.Cocycle.equivHomShift.symm
        (CochainComplex.mappingCone.fst (relativeSectionRestriction T U I))) ≫
    (shiftFunctorAdd _ (1 : ℤ) (-1 : ℤ)).inv.app _ ≫
    (shiftFunctorZero _ ℤ).hom.app _

end AlgebraicGeometry.Etale
