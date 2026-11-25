/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartTensorNaturality

@[expose] public section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Extending a chain complex by zero, then applying two zero-preserving
functors, still has zero terms in positive cochain degrees. -/
theorem tensorResolution_extended_two_functors_isZero
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    (L : HomologicalComplex C (.down ℕ)) (i : ℤ) (hi : 0 < i) :
    IsZero (((G.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj
        (L.extend ComplexShape.embeddingDownNat))).X i) := by
  change IsZero (G.obj (F.obj ((L.extend ComplexShape.embeddingDownNat).X i)))
  apply G.map_isZero
  apply F.map_isZero
  apply L.isZero_extend_X ComplexShape.embeddingDownNat
  intro j hj
  change -(j : ℤ) = i at hj
  omega

end AlgebraicGeometry
