/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # The canonical model of a diagonal right derived functor

Source: Stacks Project, Tag 070G, derived functors computed by K-injectives.
(blueprint: lem-diagonal-canonical-right-derived).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b v w r
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

variable {C : Type a} {D : Type b} [Category.{v} C] [Category.{w} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{r} C] [HasDerivedCategory.{r} D]

omit [HasDerivedCategory C] in
private theorem canonicalDerives (F : C ⥤ D) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism C).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro X Y f hf
  have : X.obj.IsKInjective := X.property
  have : Y.obj.IsKInjective := Y.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

/-- The full canonical unit on cochain complexes.
Source: Stacks Tag 070G. (blueprint: lem-diagonal-canonical-right-derived). -/
def canonicalDiagonalUnit (F : C ⥤ D) [F.Additive]
    [Abelian.HasKInjectiveResolutions C] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K := F.rightDerivedFunctorUnitQ K
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

/-- The canonical cochain unit is universal, since it computes on K-injectives.
Source: Stacks Tag 070G. (blueprint: lem-diagonal-canonical-right-derived). -/
theorem canonicalDiagonalUnit_universal (F : C ⥤ D) [F.Additive]
    [Abelian.HasKInjectiveResolutions C] :
    F.rightDerivedFunctor.IsRightDerivedFunctor (canonicalDiagonalUnit F)
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  apply (canonicalDerives F).isRightDerivedFunctor_of_isIso
  intro I
  have : I.obj.IsKInjective := I.property
  change IsIso (F.rightDerivedFunctorUnitQ I.obj)
  rw [F.rightDerivedFunctorUnitQ_eq]
  infer_instance

/-- The published right derived functor with its complete unit on complexes,
K-injective computation, shift structure and triangulation.

Source: Stacks Project, Tag 070G, and the library's canonical right derived
functor. (blueprint: lem-diagonal-canonical-right-derived).

Proof of the fields: a quasi-isomorphism between K-injective complexes is a
homotopy equivalence. The additive functor preserves that homotopy equivalence,
so the K-injective localizer derives the functor. Its canonical unit is an
isomorphism on K-injectives, which proves its universal property. The canonical
right derived functor supplies the shift and triangulated structures. -/
def canonicalDiagonalRightDerived (F : C ⥤ D) [F.Additive]
    [Abelian.HasKInjectiveResolutions C] : DiagonalRightDerived F where
  R := F.rightDerivedFunctor
  η := canonicalDiagonalUnit F
  universal := canonicalDiagonalUnit_universal F
  computation K hK := by
    let : K.IsKInjective := hK
    change IsIso (F.rightDerivedFunctorUnitQ K)
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  triangulated := inferInstance

end AlgebraicGeometry.ProEtale
