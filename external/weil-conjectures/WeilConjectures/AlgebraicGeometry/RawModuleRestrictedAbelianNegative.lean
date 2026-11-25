/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawDiagram
public import WeilConjectures.AlgebraicGeometry.RestrictedOverAbelianComplexData
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.Algebra.Category.Grp.Zero
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The negative-degree raw module and restricted abelian groups are zero,
so their unique isomorphisms are natural.
Source: Stacks Project, Tags 03FD and 03Q8; negative-degree vanishing of
right derived sections and orthogonality of the standard derived t-structure.
(blueprint: lem-sbc-raw-module-restricted-abelian-negative).

Proof: The source of raw derived Hom is concentrated in degree zero. Its target
is a degree-zero sheaf shifted by q < 0, hence is concentrated in degrees at
least -q > 0. Orthogonality of the standard t-structure makes every such morphism
zero. Restricted abelian cohomology is homology of right derived global sections
of a sheaf in degree zero. An injective resolution starts in degree zero, so the
result is concentrated in nonnegative degrees and its degree-q homology is zero.
Any two zero objects have a unique isomorphism. Both sides of the naturality
square have zero source and are therefore equal. This also applies to an empty
scheme or test object and to q = -1. -/
theorem exists_rawModule_restrictedAbelian_negative
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale)
    (hq : q < 0) :
    ∃ e : ∀ A : Over W,
      (higherDirectImageRawOverFunctor Λ k G q U).obj (op A) ≅
        restrictedOverCohomology k
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
          q A U,
      ∀ (A B : Over W) (f : A ⟶ B),
        (higherDirectImageRawOverFunctor Λ k G q U).map f.op ≫ (e A).hom =
          (e B).hom ≫ restrictedOverCohomologyMap k
            ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
            q f U := by
  classical
  have hraw (A : Over W) :
      IsZero ((higherDirectImageRawOverFunctor Λ k G q U).obj (op A)) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.2
    change Subsingleton
      (((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((A.hom ≫ k)^*[ModuleCat.{u + 1} Λ]).obj ((freeSheaf Λ S).obj U))) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (((A.hom)^*[ModuleCat.{u + 1} Λ]).obj G))⟦q⟧)
    apply subsingleton_of_forall_eq 0
    intro f
    have := DerivedCategory.Plus.TStructure.t.isGE_shift
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        (((A.hom)^*[ModuleCat.{u + 1} Λ]).obj G)) 0 q (-q) (by omega)
    exact DerivedCategory.Plus.TStructure.t.zero f 0 (-q) (by omega)
  have hres (A : Over W) :
      IsZero (restrictedOverCohomology k
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)
        q A U) := by
    let X := pullback U.hom (A.hom ≫ k)
    let F := (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom (A.hom ≫ k))).obj
      (restrictedOverCoefficient
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) A)
    change IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} q).obj
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj F)))
    have := Functor.isGE_rightDerivedFunctor_obj_singleFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}) F
    exact DerivedCategory.isZero_of_isGE _ 0 q hq
  refine ⟨fun A ↦ (hraw A).iso (hres A), ?_⟩
  intro A B f
  exact (hraw B).eq_of_src _ _
end AlgebraicGeometry.Etale
