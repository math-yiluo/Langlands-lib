/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-!
# Right derived functors of transported functors precomposed with an exact functor

Let `F`, `G` be additive autoequivalences of abelian categories `C`, `D`, and let
`e : L ⋙ G ≅ F ⋙ L` transport an additive functor `L : C ⥤ D` to
`mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`. Let `T` be an exact endofunctor of
`IsoAlgebra F` which, after forgetting the algebra structures, is a functor `T₀` preserving
K-injective complexes.

The K-injective complexes of `IsoAlgebra F` are not detected on underlying complexes, so `T`
need not preserve them; but the underlying complex of `T K` is K-injective for every K-injective
`K`, which suffices for the unit of `R(mapOfNatIso e)` to be an isomorphism at `T K`
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_rightDerivedFunctorUnit_app_mapOfNatIso`). Hence
`R(T ⋙ mapOfNatIso e) ≅ D(T) ⋙ R(mapOfNatIso e)`
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorCompMapOfNatIsoIso`).
-/

@[expose] public section

universe w w' v v' u u'

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [Abelian C] {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  [HasColimitsOfShape (Discrete ℤ) C] [HasExactColimitsOfShape (Discrete ℤ) C]
  {D : Type u'} [Category.{v'} D] [Abelian D] {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w'} (IsoAlgebra G)]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)] [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]
  (T : IsoAlgebra F ⥤ IsoAlgebra F) [T.Additive] [PreservesFiniteLimits T]
  [PreservesFiniteColimits T] {T₀ : C ⥤ C} [T₀.Additive] [T₀.PreservesKInjectiveComplexes]

omit [HasDerivedCategory.{w} (IsoAlgebra F)] [HasDerivedCategory.{w} C]
  [Abelian.HasKInjectiveResolutions (IsoAlgebra F)] [Abelian.HasKInjectiveResolutions C]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- If `T` is exact and its underlying functor `T₀` preserves K-injective complexes, the underlying
complex of `T K` is K-injective for every K-injective complex `K` of algebras. -/
lemma isKInjective_forget_map_map (α : T ⋙ forget F ≅ forget F ⋙ T₀)
    (K : CochainComplex (IsoAlgebra F) ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  have : CochainComplex.IsKInjective ((T₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := inferInstance
  have : CochainComplex.IsKInjective
      (((forget F ⋙ T₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    CochainComplex.isKInjective_of_iso (L₁ := (T₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((forget F).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (forget F ⋙ T₀)) (ComplexShape.up ℤ)).app K)
  exact CochainComplex.isKInjective_of_iso
    ((Functor.mapHomologicalComplexCompIso α (ComplexShape.up ℤ)).app K).symm

/-- If `T` is exact and its underlying functor preserves K-injective complexes, then
`D(T) ⋙ R(mapOfNatIso e)` is a right derived functor of `T ⋙ mapOfNatIso e`. -/
lemma isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_mapOfNatIso
    (α : T ⋙ forget F ≅ forget F ⋙ T₀) :
    (T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor).IsRightDerivedFunctor
      (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e))
      (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((T ⋙ mapOfNatIso e).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e)).app
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
  have := isKInjective_forget_map_map T α K
  have h₂ := isIso_rightDerivedFunctorUnit_app_mapOfNatIso e
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have h₂' : IsIso ((mapOfNatIso e).rightDerivedFunctorUnit.app
      ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) := h₂
  have h₃ : IsIso ((mapOfNatIso e).rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :=
    inferInstanceAs (IsIso ((mapOfNatIso e).rightDerivedFunctor.mapIso
      (T.mapDerivedCategoryFactorsh.app _).symm).hom)
  rw [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  infer_instance

/-- **Right derived functors of transported functors precomposed with an exact functor**:
`R(T ⋙ mapOfNatIso e) ≅ D(T) ⋙ R(mapOfNatIso e)`, for an exact endofunctor `T` of algebras
whose underlying functor preserves K-injective complexes. -/
noncomputable def rightDerivedFunctorCompMapOfNatIsoIso (α : T ⋙ forget F ≅ forget F ⋙ T₀) :
    (T ⋙ mapOfNatIso e).rightDerivedFunctor ≅
      T.mapDerivedCategory ⋙ (mapOfNatIso e).rightDerivedFunctor :=
  have := isRightDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor_mapOfNatIso e T α
  Functor.rightDerivedUnique _ _ (T ⋙ mapOfNatIso e).rightDerivedFunctorUnit
    (Functor.mapDerivedCategoryCompRightDerivedFunctorUnit T (mapOfNatIso e))
    (HomotopyCategory.quasiIso (IsoAlgebra F) (ComplexShape.up ℤ))

end CategoryTheory.Endofunctor.IsoAlgebra
