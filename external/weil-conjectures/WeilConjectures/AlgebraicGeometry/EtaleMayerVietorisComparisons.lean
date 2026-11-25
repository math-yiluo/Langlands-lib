/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Cohomology on Sites, Tag 03F3 (2).
(blueprint: lem-weil-pbc-etale-mayer-vietoris-comparisons)

Proof: Choose a bounded below injective resolution of a sheaf on X's small etale site.
Evaluation at each of X, U, V and U ∩ V computes its right derived evaluation functor.
For an open immersion, inverse image is restriction to the localized site and preserves
injectives: extension by zero is its exact left adjoint. Thus restriction of the resolution
is an injective resolution on that open. Global sections of the restricted resolution
are naturally the sections of the original resolution on the corresponding etale object.
Taking homology identifies right derived evaluation with derived global sections of the
restricted sheaf in degree zero. At X use the same resolution without restriction.
Comparison maps between resolutions are unique up to homotopy, so these identifications
are natural in the sheaf and give the four functor isomorphisms, independently in every
nonnegative degree. No covering assumption is needed. -/
theorem etale_mayerVietoris_comparisons (X : Scheme.{u}) (U V : X.Opens) :
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived n ≅
      (DerivedCategory.singleFunctor _ 0 ⋙ cohomology AddCommGrpCat.{u + 1} X n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk U.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} U.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} U.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk V.ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} V.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} V.toScheme n)) ∧
    Nonempty (∀ n : ℕ, (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (U ⊓ V).ι))).rightDerived n ≅
      (upperStar AddCommGrpCat.{u + 1} (U ⊓ V).ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology AddCommGrpCat.{u + 1} (U ⊓ V).toScheme n)) := by
  let A := AddCommGrpCat.{u + 1}
  have total (Y : Scheme.{u}) (F : Sheaf Y.smallEtaleTopology A ⥤ A)
      [F.Additive] (n : ℕ) :
      F.rightDerived n ≅ DerivedCategory.singleFunctor _ 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor A n :=
    (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0)
          F.rightDerivedFunctorPlusCompatibility) (DerivedCategory.homologyFunctor A n)
  have ambient : Nonempty (∀ n : ℕ,
      (sheafToPresheaf X.smallEtaleTopology A ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))).rightDerived n ≅
      (DerivedCategory.singleFunctor _ 0 ⋙ cohomology A X n)) := by
    let E := sheafToPresheaf X.smallEtaleTopology A ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 X)))
    let e : E ≅ Sheaf.Γ X.smallEtaleTopology A :=
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
        (MorphismProperty.Over.mkIdTerminal _ _)).symm
    exact ⟨fun n ↦ total X E n ≪≫ Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight (Functor.rightDerivedFunctorNatIso e)
        (DerivedCategory.homologyFunctor A n))⟩
  have onOpen (W : X.Opens) : Nonempty (∀ n : ℕ,
      (sheafToPresheaf X.smallEtaleTopology A ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk W.ι))).rightDerived n ≅
      (upperStar A W.ι ⋙ DerivedCategory.singleFunctor _ 0 ⋙
        cohomology A W.toScheme n)) := by
    let T := upperStar A W.ι
    let G := Sheaf.Γ W.toScheme.smallEtaleTopology A
    let E := sheafToPresheaf X.smallEtaleTopology A ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk W.ι))
    let e : T ⋙ G ≅ E :=
      Functor.isoWhiskerLeft T
        (Sheaf.ΓNatIsoSheafSections W.toScheme.smallEtaleTopology A
          (MorphismProperty.Over.mkIdTerminal _ _)) ≪≫
      Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A W.ι inferInstance)
        ((sheafSections W.toScheme.smallEtaleTopology A).obj
          (op (Scheme.Etale.mk (𝟙 W.toScheme))))
    let : T.PreservesKInjectiveComplexes :=
      (openImmersionLowerShriekUpperStarAdjunction A W.ι).preservesKInjectiveComplexes
    exact ⟨fun n ↦ total X E n ≪≫ Functor.isoWhiskerLeft
      (DerivedCategory.singleFunctor _ 0)
      (Functor.isoWhiskerRight
        ((Functor.rightDerivedFunctorNatIso e).symm ≪≫
          Functor.rightDerivedFunctorCompIso T G) (DerivedCategory.homologyFunctor A n)) ≪≫
      Functor.isoWhiskerRight T.singleFunctorCompRightDerivedFunctorIso
        (G.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor A n)⟩
  exact ⟨ambient, onOpen U, onOpen V, onOpen (U ⊓ V)⟩

end AlgebraicGeometry.Etale
