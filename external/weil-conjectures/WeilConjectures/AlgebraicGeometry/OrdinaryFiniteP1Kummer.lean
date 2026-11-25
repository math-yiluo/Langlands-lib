/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard

/-!
# Canonical arrows for the ordinary finite projective-line calculation

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-amb-p1-decomposition.md and
thm-amb-p1-adjunction.md; Stacks Project, Tags 03PL and 03FD
(auxiliary; not a blueprint node).

## Main definitions

* `ordinaryFiniteRootMap`: scalar extension of roots of unity.
* `ordinaryFiniteClass`: realization of a module-derived class in abelian cohomology.
* `ordinaryFiniteP1KummerClass`: the scalar Kummer class of the specified `O(1)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor ChangeOfRings

namespace AlgebraicGeometry.Etale

-- Reuse the proposition instances already stored in the ordinary derived category.
-- This keeps the canonical localization data identical before taking object maps.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] ModuleCat.extendScalars
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- The existing chosen derived localization, cached before its object projections.
Source: the canonical module-sheaf derived category in blueprint
proposition-adjunction-projective-line--1 (auxiliary; not a blueprint node). -/
@[instance_reducible]
def ordinaryFiniteDerivedCategoryInstance (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance 100000] ordinaryFiniteDerivedCategoryInstance

/-- The constant coefficient sheaf, in the existing finite-twist encoding.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
abbrev ordinaryFiniteConstant (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :=
  (constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)

set_option backward.isDefEq.respectTransparency false in
/-- The map from the integral constant sheaf sending one to one.
Source: Stacks, Tag 03FD (auxiliary; not a blueprint node). -/
def ordinaryFiniteIntegralGenerator (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (moduleAbelianForget A T).obj (ordinaryFiniteConstant A T) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).symm
    (AddCommGrpCat.ofHom
      ((((forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).map
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app
            (op (Scheme.Etale.mk (𝟙 T))))).hom).comp
        ((Int.castAddHom A).comp AddEquiv.ulift.toAddMonoidHom)))

/-- Degree zero in the ordinary derived category, with a stable object interface.
Source: the degree-zero construction in the ordinary Kummer class
(auxiliary; not a blueprint node). -/
def ordinaryFiniteDegreeZero (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) : DerivedCategoryModule A T :=
  (DerivedCategory.singleFunctor _ 0).obj F

/-- The degree-zero embedding, cached as a functor before taking its object map.
Source: the canonical degree-zero embedding used in the ordinary Kummer construction
(auxiliary; not a blueprint node). -/
def ordinaryFiniteSingleFunctor (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ DerivedCategoryModule A T :=
  { DerivedCategory.singleFunctor _ 0 with obj := ordinaryFiniteDegreeZero A T }

/-- The cached embedding is the canonical single-degree functor.
Source: definition of the degree-zero embedding
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteSingleFunctor_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    ordinaryFiniteSingleFunctor A T = DerivedCategory.singleFunctor _ 0 := rfl

/-- The canonical Ext/derived-morphism equivalence, with the cached embeddings.
Source: the Ext realization used in the ordinary Kummer class, Stacks Tag 03FD
(auxiliary; not a blueprint node). -/
def ordinaryFiniteExtHomEquiv (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    Ext M F n ≃ ((ordinaryFiniteSingleFunctor A T).obj M ⟶
      ((ordinaryFiniteSingleFunctor A T).obj F)⟦(n : ℤ)⟧) := by
  unfold ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
  exact Ext.homEquiv

/-- The cached equivalence is the canonical Ext/derived-morphism equivalence.
Source: Mathlib's Ext realization, Stacks Tag 03FD
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteExtHomEquiv_eq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    ordinaryFiniteExtHomEquiv A T M F n = Ext.homEquiv := rfl

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

attribute [local irreducible] ordinaryFiniteExtHomEquiv

/-- Exact forgetting and precomposition applied to an Ext representative.
Source: the ordinary Kummer realization formula, Stacks Tag 03FD
(auxiliary; not a blueprint node). -/
def ordinaryFiniteExtClassCore {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ) (x : Ext X Y n) :
    Ext.{u + 1} Z (G.obj Y) n :=
  (Ext.mk₀ e).comp (x.mapExactFunctor G) (zero_add n)

/-- Realize a derived morphism after an exact functor and a specified source map.
This generic construction keeps concrete derived localization instances abstract.
Source: the Ext composition and exact-functor APIs, Stacks Tag 03FD.
(auxiliary; not a blueprint node). -/
def ordinaryFiniteClassCore {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ)
    (c : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    Ext.{u + 1} Z (G.obj Y) n :=
  ordinaryFiniteExtClassCore G e Y n (Ext.homEquiv.symm c)

set_option backward.isDefEq.respectTransparency.types true in
/-- View a derived module class as an abelian cohomology class, by forgetting its Ext
class and precomposing with the integral generator. This is a map, not a chosen
cohomology equivalence.
Source: Stacks, Tag 03FD (auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteClass (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (c : (ordinaryFiniteSingleFunctor A T).obj (ordinaryFiniteConstant A T) ⟶
      ((ordinaryFiniteSingleFunctor A T).obj F)⟦(n : ℤ)⟧) :
    Sheaf.H ((moduleAbelianForget A T).obj F) n :=
  ordinaryFiniteExtClassCore (moduleAbelianForget A T)
    (ordinaryFiniteIntegralGenerator A T) F n
    ((ordinaryFiniteExtHomEquiv A T (ordinaryFiniteConstant A T) F n).symm c)

private theorem realize_equiv_apply {U V W : Type*} (e : U ≃ V) (f : U → W) (x : U) :
    f (e.symm (e x)) = f x := congrArg f (e.symm_apply_apply x)

/-- Realizing a cached Ext representative gives its exact-forgetting composite.
Source: the canonical Ext realization formula, Stacks Tag 03FD
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteClass_extHomEquiv
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (x : Ext (ordinaryFiniteConstant A T) F n) :
    ordinaryFiniteClass A T F n (ordinaryFiniteExtHomEquiv A T _ F n x) =
      ordinaryFiniteExtClassCore (moduleAbelianForget A T)
        (ordinaryFiniteIntegralGenerator A T) F n x := by
  unfold ordinaryFiniteClass
  exact realize_equiv_apply
    (ordinaryFiniteExtHomEquiv A T (ordinaryFiniteConstant A T) F n)
    (ordinaryFiniteExtClassCore (moduleAbelianForget A T)
      (ordinaryFiniteIntegralGenerator A T) F n) x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarUnitComposite_naturality (R : Type) (S : Type (u + 1))
    [CommRing R] [CommRing S] (r : R →+* S)
    {M M' : ModuleCat.{u + 1} R} {P P' : ModuleCat.{u + 1} S}
    (f : M ⟶ M') (g : P ⟶ P')
    (s : (ModuleCat.extendScalars r).obj M ⟶ P)
    (s' : (ModuleCat.extendScalars r).obj M' ⟶ P')
    (h : (ModuleCat.extendScalars r).map f ≫ s' = s ≫ g) :
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).map f ≫
        AddCommGrpCat.ofHom
          ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
            r s').hom.toAddMonoidHom) =
      AddCommGrpCat.ofHom
        ((ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
          r s).hom.toAddMonoidHom) ≫
        (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}).map g := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u + 1, 0, u + 1} r
  have hh := congrArg (adj.homEquiv M P') h
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at hh
  apply AddCommGrpCat.ext
  intro x
  exact congrArg (fun k ↦ k x) hh

attribute [local irreducible]
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
  Scheme.finiteEtaleTwistScalar

/-- The canonical scalar map on roots of unity, `z ↦ 1 ⊗ z`, on sections.
Source: Stacks, Tag 03PK (auxiliary; not a blueprint node). -/
def ordinaryFiniteRootGenerator (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (W : T.Etaleᵒᵖ) :
    (T.rootsOfUnitySheaf N).obj.obj W →+
      ((moduleAbelianForget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA)).obj.obj W :=
  let M := Scheme.finiteEtaleMuModuleObj T N W
  let P := (Scheme.finiteEtaleTateLine T N A hA).obj.obj W
  let σ : (ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA)).obj M ⟶ P :=
    (toSheafify T.smallEtaleTopology (Scheme.finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA))).app W
  (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{0, u + 1, u + 1}
    (Scheme.finiteEtaleTwistScalar N A hA) σ).hom.toAddMonoidHom

/-- Naturality of the scalar map `z ↦ 1 ⊗ z`.
Source: Stacks, Tag 03PK (auxiliary; not a blueprint node).
Proof: the scalar-extension unit is natural and the sheafification unit is natural;
compose their two squares. Their underlying maps are the displayed section maps. -/
theorem ordinaryFiniteRootGenerator_naturality (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    {W V : T.Etaleᵒᵖ} (f : W ⟶ V) :
    (T.rootsOfUnitySheaf N).obj.map f ≫
        AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T V) =
      AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T W) ≫
        ((moduleAbelianForget A T).obj
          (Scheme.finiteEtaleTateLine T N A hA)).obj.map f := by
  unfold ordinaryFiniteRootGenerator
  exact scalarUnitComposite_naturality (ZMod N) A
    (Scheme.finiteEtaleTwistScalar N A hA)
    ((Scheme.finiteEtaleMuModulePresheaf T N).map f)
    ((Scheme.finiteEtaleTateLine T N A hA).obj.map f)
    _ _ ((toSheafify T.smallEtaleTopology (Scheme.finiteEtaleMuModulePresheaf T N ⋙
      ModuleCat.extendScalars (Scheme.finiteEtaleTwistScalar N A hA))).naturality f)

/-- Scalar extension of roots of unity, as an abelian sheaf map.
Source: Stacks, Tag 03PK (auxiliary; not a blueprint node). -/
def ordinaryFiniteRootMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) :
    T.rootsOfUnitySheaf N ⟶
      (moduleAbelianForget A T).obj
        (Scheme.finiteEtaleTateLine T N A hA) :=
  ⟨{ app := fun W ↦ AddCommGrpCat.ofHom (ordinaryFiniteRootGenerator A N hA T W)
     naturality := fun _ _ f ↦ ordinaryFiniteRootGenerator_naturality A N hA T f }⟩

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map

/-- The twist line placed in degree zero, using the existing finite etale twist.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
abbrev ordinaryFiniteLine (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) : DerivedCategoryModule A T :=
  ordinaryFiniteDegreeZero A T (Scheme.finiteEtaleTateLine T N A hA)

/-- The untwisted coefficient sheaf in degree zero.
Source: blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
abbrev ordinaryFiniteUnit (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    DerivedCategoryModule A T :=
  ordinaryFiniteDegreeZero A T (ordinaryFiniteConstant A T)

/-- The scalar-extended Kummer class of a specified Picard class on any scheme.
Source: the Kummer boundary and coefficient map, Stacks Tags 03PK and 03PL
(auxiliary; not a blueprint node). -/
def ordinaryFiniteKummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (L : T.Pic) :
    Sheaf.H ((moduleAbelianForget A T).obj (Scheme.finiteEtaleTateLine T N A hA)) 2 :=
  Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
    (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T L))

/-- The Picard class of the canonical O(1) on the projective line.
Source: blueprint lemma-cohomology-projective-line-trace and Stacks Tag 03PL
(auxiliary; not a blueprint node). -/
def ordinaryFiniteP1PicardClass (S : Scheme.{u}) : (ProjectiveLine S).Pic :=
  Scheme.Pic.ofIsInvertible (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)

/-- The actual scalar-extended Kummer Chern class in abelian cohomology.
The Picard class is that of the existing `ProjectiveSpace.twist ... 1`, whose
transition is `g₀ = (x₁/x₀)⁻¹ g₁`.
Source: Stacks, Tag 03PL; blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteP1KummerClass (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤))) :
    Sheaf.H ((moduleAbelianForget A (ProjectiveLine S)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA)) 2 :=
  ordinaryFiniteKummerClass A N hA (ProjectiveLine S) hP (ordinaryFiniteP1PicardClass S)

set_option backward.isDefEq.respectTransparency false in
/-- The Chern-class specification predicate used by the normalized datum.
Source: Stacks Tag 03PL (auxiliary; not a blueprint node). -/
def ordinaryFiniteP1ChernSpec (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u})
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) : Prop :=
  ordinaryFiniteClass A (ProjectiveLine S)
      (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2 c =
    ordinaryFiniteP1KummerClass A N hA S hP

/-- The Chern specification is the scalar-extended Kummer class of O(1).
Source: the defining normalization, blueprint lemma-cohomology-projective-line-trace
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteP1ChernSpec_iff
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    ordinaryFiniteP1ChernSpec A N hA S hP c ↔
      ordinaryFiniteClass A (ProjectiveLine S)
          (Scheme.finiteEtaleTateLine (ProjectiveLine S) N A hA) 2 c =
        ordinaryFiniteKummerClass A N hA (ProjectiveLine S) hP
          (ordinaryFiniteP1PicardClass S) := by
  unfold ordinaryFiniteP1ChernSpec ordinaryFiniteP1KummerClass
  rfl

end AlgebraicGeometry.Etale
