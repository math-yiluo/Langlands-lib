/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawModuleAbelianHomMap
import WeilConjectures.CategoryTheory.DerivedSourceComparisonInjective
import WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceHomBijective
import WeilConjectures.AlgebraicGeometry.RawModuleFreeSourceAcyclic

/-! # Injective raw scalar comparison

Source: Stacks Project, Tag 03FD, injective-resolution comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Injective of the raw scalar comparison on underlying groups.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: lem-sbc-raw-module-abelian-hom-map-injective).

Proof: Let two module derived classes have the same image and subtract them.
Resolve A.hom^*G by injective module sheaves and represent the difference by a
cocycle in sections over V = U times_S A.left. Free represented sheaves
corepresent sections after pullback. Forgetting scalars leaves the section
complex unchanged, and Tag 03FD says its terms are acyclic for abelian sections.
Thus its cohomology also computes the target abelian derived Hom group. The
explicit scalar map carries the chosen cocycle to the identical section cocycle:
freeMap sends the identity generator to itself, and the pullback, single and
shift comparisons are the canonical adjunction identifications. Its image being
zero means this section cocycle is a boundary in that same complex. The identical
boundary is a boundary in the module section complex, so the original difference
class is zero. Additivity now proves equality of the two original classes.
The argument applies to degree zero (where boundaries in degree -1 are zero),
the zero ring and empty V. -/
theorem rawModuleAbelianHomMap_injective
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    Function.Injective (rawModuleAbelianHomMap Λ k G q U A).hom := by
  let V := moduleAbelianForget Λ A.left
  let F := (upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G
  let L := (upperStar (ModuleCat.{u + 1} Λ) (A.hom ≫ k)).obj ((freeSheaf Λ S).obj U)
  let B := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).obj
    (RawModuleScalarComparison.freeAbelian S U)
  let a : B ⟶ V.obj L := (upperStar AddCommGrpCat.{u + 1} (A.hom ≫ k)).map
    (RawModuleScalarComparison.freeMap Λ S U) ≫
      RawModuleScalarComparison.pullback Λ (A.hom ≫ k) ((freeSheaf Λ S).obj U)
  have hhom (I : Sheaf A.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (_ : Injective I) : Function.Bijective (fun f : L ⟶ I ↦ a ≫ V.map f) := by
    exact rawModuleFreeSourceHom_bijective Λ (A.hom ≫ k) U I
  have hac (I : Sheaf A.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (hI : Injective I) : (preadditiveCoyoneda.obj (op B)).rightAcyclic (V.obj I) := by
    have : Injective I := hI
    exact rawModuleFreeSource_acyclic Λ (A.hom ≫ k) U I
  have h := derivedSourceComparison_injective V L B a hhom hac F q
  let b := (V.mapDerivedCategoryPlus.commShiftIso (q : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
    (shiftFunctor _ (q : ℤ)).map
      ((V.mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          (inv (RawModuleScalarComparison.pullback Λ A.hom G)))
  have : IsIso b := by dsimp only [b]; infer_instance
  let c := (DerivedCategory.Plus.singleFunctor _ 0).map a ≫
    (V.mapDerivedCategoryPlusSingleFunctor 0).inv.app L
  change Function.Injective (fun x : (DerivedCategory.Plus.singleFunctor _ 0).obj L ⟶
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧ ↦
      c ≫ (V.mapDerivedCategoryPlus.map x ≫ b))
  intro x y hxy
  apply h
  apply (cancel_mono b).1
  exact (Category.assoc c _ b).trans (hxy.trans (Category.assoc c _ b).symm)

end AlgebraicGeometry.Etale
