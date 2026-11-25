/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Composition of total right derived functors

Let `F : C ⥤ D` and `G : D ⥤ E` be additive functors between abelian categories with
K-injective resolutions. This file proves the Grothendieck composition theorem for the
total right derived functors on the unbounded derived categories: if `F` sends
K-injective complexes to K-injective complexes, then the canonical comparison

`R(F ⋙ G) ≅ RF ⋙ RG`

is an isomorphism (`Functor.rightDerivedFunctorCompIso`). The composite `RF ⋙ RG`,
equipped with the composite unit `Functor.rightDerivedFunctorCompUnit`, is itself a right
derived functor of `(F ⋙ G).mapHomotopyCategory ⋙ Qh`: by the K-injective right
derivability structure it suffices to check that the composite unit is an isomorphism on
K-injective complexes, which holds since the unit of `RF` is an isomorphism on K-injective
complexes and the unit of `RG` is an isomorphism on their images under `F`. The
isomorphism then follows from the uniqueness of right derived functors.

The K-injectivity hypothesis is packaged as the type class
`Functor.PreservesKInjectiveComplexes`, for which the main criterion is
`CategoryTheory.Adjunction.preservesKInjectiveComplexes`: a right adjoint of an *exact*
functor preserves K-injective complexes. (For the intended application, the pushforward
`f_*` of étale sheaves is right adjoint to the exact pullback `f^*`, so that the Leray
composition isomorphism `RΓ(Y, Rf_* K) ≅ RΓ(X, K)` becomes an instance of the theorem;
see `Etale.derivedGlobalSectionsComp`.) The proof of the criterion uses the induced
adjunction on categories of homological complexes,
`CategoryTheory.Adjunction.mapHomologicalComplex`, and transport of null-homotopies along
the adjunction.

The file also records the functoriality of the total right derived functor in natural
transformations (`Functor.rightDerivedFunctorNatTrans`,
`Functor.rightDerivedFunctorNatIso`), so that a composition `F ⋙ G ≅ H` of underived
functors yields `RF ⋙ RG ≅ RH` in one step
(`Functor.rightDerivedFunctorCompIso'`).

## Main definitions

- `CategoryTheory.Functor.PreservesKInjectiveComplexes`: the class of additive functors
  sending K-injective complexes to K-injective complexes, with the criterion
  `CategoryTheory.Adjunction.preservesKInjectiveComplexes` for right adjoints of exact
  functors and its special case
  `CategoryTheory.Functor.preservesKInjectiveComplexes_of_isEquivalence` for equivalences.
- `CategoryTheory.Functor.rightDerivedFunctorNatTrans` and
  `Functor.rightDerivedFunctorNatIso`: functoriality of the total right derived functor.
- `CategoryTheory.Functor.rightDerivedFunctorCompIso`: the composition isomorphism
  `R(F ⋙ G) ≅ RF ⋙ RG`.
- `CategoryTheory.Functor.rightDerivedFunctorCompIso'`: the composition isomorphism
  `RF ⋙ RG ≅ RH` associated with an isomorphism `F ⋙ G ≅ H`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

section PreservesKInjective

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- An additive functor `F` between abelian categories *preserves K-injective complexes*
if the image of any K-injective cochain complex under `F.mapHomologicalComplex` is
K-injective. This is the hypothesis under which the composition of total right derived
functors is the total right derived functor of the composition, see
`Functor.rightDerivedFunctorCompIso`. -/
class Functor.PreservesKInjectiveComplexes (F : C ⥤ D) [F.Additive] : Prop where
  isKInjective_map (K : CochainComplex C ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

instance (F : C ⥤ D) [F.Additive] [F.PreservesKInjectiveComplexes]
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Functor.PreservesKInjectiveComplexes.isKInjective_map K

/-- A right adjoint of an *exact* functor preserves K-injective complexes: a morphism
from an acyclic complex `M` into the image of a K-injective complex `K` corresponds by
adjunction to a morphism from the acyclic complex `G(M)` into `K`, whose null-homotopy
transports back along the adjunction. -/
lemma Adjunction.preservesKInjectiveComplexes {G : D ⥤ C} {F : C ⥤ D} (adj : G ⊣ F)
    [G.Additive] [F.Additive] [G.PreservesHomology] :
    F.PreservesKInjectiveComplexes where
  isKInjective_map K _ := by
    constructor
    intro M g hM
    have hM' : ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).Acyclic := hM.map G
    let adjc := adj.mapHomologicalComplex (ComplexShape.up ℤ)
    let g' := (adjc.homEquiv M K).symm g
    have hg : g = adjc.unit.app M ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map g' := by
      have h := (adjc.homEquiv M K).apply_symm_apply g
      rw [Adjunction.homEquiv_unit] at h
      exact h.symm
    have hzero : adjc.unit.app M ≫ (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (0 : (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ⟶ K) = 0 := by
      simp
    exact ⟨(Homotopy.ofEq hg).trans
      (((F.mapHomotopy
        (CochainComplex.IsKInjective.homotopyZero g' hM')).compLeft (adjc.unit.app M)).trans
        (Homotopy.ofEq hzero))⟩

/-- An additive equivalence preserves K-injective complexes, being right adjoint to its
inverse, which is exact. -/
instance Functor.preservesKInjectiveComplexes_of_isEquivalence (F : C ⥤ D) [F.Additive]
    [F.IsEquivalence] : F.PreservesKInjectiveComplexes :=
  have : F.asEquivalence.functor.Additive := ‹F.Additive›
  have : F.asEquivalence.symm.functor.Additive := F.asEquivalence.inverse_additive
  F.asEquivalence.symm.toAdjunction.preservesKInjectiveComplexes

end PreservesKInjective

namespace Functor

section NatTrans

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]

/-- Functoriality of the total right derived functor: a natural transformation `F ⟶ G`
of additive functors induces a natural transformation
`RF ⟶ RG : DerivedCategory C ⥤ DerivedCategory D` of the total right derived
functors. -/
noncomputable def rightDerivedFunctorNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) : F.rightDerivedFunctor ⟶ G.rightDerivedFunctor :=
  rightDerivedNatTrans F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- Functoriality of the total right derived functor in natural isomorphisms:
an isomorphism `F ≅ G` of additive functors induces an isomorphism `RF ≅ RG` of the
total right derived functors. -/
noncomputable def rightDerivedFunctorNatIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) : F.rightDerivedFunctor ≅ G.rightDerivedFunctor where
  hom := rightDerivedFunctorNatTrans e.hom
  inv := rightDerivedFunctorNatTrans e.inv
  hom_inv_id := by
    simp [rightDerivedFunctorNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategory_comp]
  inv_hom_id := by
    simp [rightDerivedFunctorNatTrans, ← Functor.whiskerRight_comp,
      ← NatTrans.mapHomotopyCategory_comp]

/-- The natural transformation induced on total right derived functors by a natural
isomorphism is an isomorphism. -/
instance isIso_rightDerivedFunctorNatTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) [IsIso τ] : IsIso (rightDerivedFunctorNatTrans τ) :=
  (inferInstanceAs (IsIso (rightDerivedFunctorNatIso (asIso τ)).hom))

end NatTrans

section Composition

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

/-- The composite unit exhibiting `RF ⋙ RG` as a candidate right derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`: it is assembled from the units of `RF` and `RG` and
the composition isomorphism of `mapHomotopyCategory`. -/
noncomputable def rightDerivedFunctorCompUnit :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.rightDerivedFunctorUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorUnit G.rightDerivedFunctor ≫
    (Functor.associator _ _ _).hom

/-- If `F` preserves K-injective complexes, then `RF ⋙ RG`, equipped with the composite
unit, is a right derived functor of `(F ⋙ G).mapHomotopyCategory ⋙ Qh`: by the
K-injective right derivability structure it suffices that the composite unit is an
isomorphism on K-injective complexes, which holds since the units of `RF` and `RG` are
isomorphisms on K-injective complexes and `F` preserves K-injectivity. -/
instance isRightDerivedFunctor_rightDerivedFunctor_comp [F.PreservesKInjectiveComplexes] :
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor).IsRightDerivedFunctor
      (rightDerivedFunctorCompUnit F G) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  refine (HomotopyCategory.KInjectives.localizerMorphism_derives
    ((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)).isRightDerivedFunctor_of_isIso _ (fun X₁ => ?_)
  obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X₁
  change IsIso ((rightDerivedFunctorCompUnit F G).app
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  have h₁ : IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K)) := inferInstance
  have h₂ : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := inferInstance
  have h₂' : IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K).as))) := h₂
  dsimp [rightDerivedFunctorCompUnit]
  infer_instance

/-- **Composition of total right derived functors**: for additive functors `F : C ⥤ D`
and `G : D ⥤ E` between abelian categories with K-injective resolutions, where `F`
preserves K-injective complexes (e.g. `F` is a right adjoint of an exact functor,
`Adjunction.preservesKInjectiveComplexes`), the canonical comparison
`R(F ⋙ G) ≅ RF ⋙ RG` is an isomorphism. -/
noncomputable def rightDerivedFunctorCompIso [F.PreservesKInjectiveComplexes] :
    (F ⋙ G).rightDerivedFunctor ≅ F.rightDerivedFunctor ⋙ G.rightDerivedFunctor :=
  rightDerivedUnique (F ⋙ G).rightDerivedFunctor
    (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (F ⋙ G).rightDerivedFunctorUnit (rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

/-- The composition isomorphism `RF ⋙ RG ≅ RH` associated with an isomorphism
`F ⋙ G ≅ H` of additive functors, for `F` preserving K-injective complexes. This is the
form in which the composition theorem is usually applied, e.g. for the Leray
isomorphism `RΓ(Y, Rf_* K) ≅ RΓ(X, K)`. -/
noncomputable def rightDerivedFunctorCompIso' {H : C ⥤ E} [H.Additive]
    [F.PreservesKInjectiveComplexes] (e : F ⋙ G ≅ H) :
    F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor :=
  (rightDerivedFunctorCompIso F G).symm ≪≫ rightDerivedFunctorNatIso e

end Composition

end Functor

end CategoryTheory
