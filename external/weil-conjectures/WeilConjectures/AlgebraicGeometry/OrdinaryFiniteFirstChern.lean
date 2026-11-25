/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase

/-! # Canonical derived Chern arrows

The inverse of the proved class bijection determines every arrow uniquely.
Source: Stacks 03PL and 03FD, the Kummer connecting class and its realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Scheme.finiteEtaleTateLine Scheme.kummerδ₁
  AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor
  ordinaryFiniteRootMap Sheaf.H.map Scheme.Pic.toCohomologicalPicardGroup Scheme.Pic.map

/-- The existing class bijection, on the recorded degree-zero objects.
Source: ordinaryFiniteClass_bijective_arbitraryBase
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteClassEquiv (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :=
  Equiv.ofBijective (ordinaryFiniteClass A T F n)
    (ordinaryFiniteClass_bijective_arbitraryBase A T F n)

section
attribute [local semireducible] ordinaryFiniteClassEquiv

/-- The bundled bijection is the existing realization.
Source: the definition of Equiv.ofBijective
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteClassEquiv_apply (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ)
    (c : ordinaryFiniteUnit A T ⟶ (ordinaryFiniteDegreeZero A T F)⟦(n : ℤ)⟧) :
    ordinaryFiniteClassEquiv A T F n c = ordinaryFiniteClass A T F n c := by
  rfl

end

/-- The unique derived arrow realizing the scalar Kummer class of a line bundle.
The inverse bijection fixes the arrow uniquely, rather than choosing an arbitrary witness.
Source: Stacks 03PL, 03FD and ordinaryFiniteClass_bijective_arbitraryBase.
(auxiliary; not a blueprint node). -/
@[irreducible]
def ordinaryFiniteFirstChern (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (M : T.Pic) :
    ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧ :=
  (ordinaryFiniteClassEquiv A T (Scheme.finiteEtaleTateLine T N A hA) 2).symm
    (Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
      (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T M)))

/-- The class of the canonical derived Chern arrow is its defining Kummer class.
Source: inverse-bijection cancellation (auxiliary; not a blueprint node). -/
theorem ordinaryFiniteFirstChern_class (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (M : T.Pic) :
    ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
        (ordinaryFiniteFirstChern A N hA T hT M) =
      Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
        (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T M)) := by
  unfold ordinaryFiniteFirstChern
  exact (ordinaryFiniteClassEquiv_apply A T
    (Scheme.finiteEtaleTateLine T N A hA) 2 _).symm.trans
      ((ordinaryFiniteClassEquiv A T
        (Scheme.finiteEtaleTateLine T N A hA) 2).apply_symm_apply _)

/-- A specified Kummer realization equals the canonical derived Chern arrow.
Source: injectivity of the class bijection
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteFirstChern_unique (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (M : T.Pic)
    (c : ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 c =
      Sheaf.H.map (ordinaryFiniteRootMap A N hA T) 2
        (T.kummerδ₁ N hT (Scheme.Pic.toCohomologicalPicardGroup T M))) :
    c = ordinaryFiniteFirstChern A N hA T hT M := by
  apply (ordinaryFiniteClass_bijective_arbitraryBase A T
    (Scheme.finiteEtaleTateLine T N A hA) 2).injective
  exact hc.trans (ordinaryFiniteFirstChern_class A N hA T hT M).symm

private theorem finiteClassCore_add {C : Type*} {D : Type*}
    [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X : C} {Z : D} (e : Z ⟶ G.obj X) (Y : C) (n : ℕ)
    (x y : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    ordinaryFiniteClassCore G e Y n (x + y) =
      ordinaryFiniteClassCore G e Y n x + ordinaryFiniteClassCore G e Y n y := by
  unfold ordinaryFiniteClassCore ordinaryFiniteExtClassCore
  rw [show Ext.homEquiv.symm (x + y) = Ext.homEquiv.symm x + Ext.homEquiv.symm y from
    Ext.homAddEquiv.symm.map_add x y, Ext.mapExactFunctor_add, Ext.comp_add]

/-- Tensor products of line bundles give sums of canonical derived Chern arrows.
Source: additivity of the Kummer connecting map and of the Ext realization
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteFirstChern_mul (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) (M L : T.Pic) :
    ordinaryFiniteFirstChern A N hA T hT (M * L) =
      ordinaryFiniteFirstChern A N hA T hT M + ordinaryFiniteFirstChern A N hA T hT L := by
  apply (ordinaryFiniteClass_bijective_arbitraryBase A T
    (Scheme.finiteEtaleTateLine T N A hA) 2).injective
  have hadd (x y : ordinaryFiniteUnit A T ⟶ (ordinaryFiniteLine A N hA T)⟦(2 : ℤ)⟧) :
      ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 (x + y) =
        ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 x +
          ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 y := by
    unfold ordinaryFiniteClass
    exact finiteClassCore_add (moduleAbelianForget A T)
      (ordinaryFiniteIntegralGenerator A T) (Scheme.finiteEtaleTateLine T N A hA) 2 x y
  rw [hadd, ordinaryFiniteFirstChern_class, ordinaryFiniteFirstChern_class,
    ordinaryFiniteFirstChern_class, Scheme.Pic.toCohomologicalPicardGroup_mul,
    map_add, map_add]

/-- Canonical derived Chern arrows commute with the normalized pullback comparison.
Source: naturality of scalar Kummer realization and uniqueness of the class
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteFirstChern_pullback (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤))) (M : Y.Pic) :
    ordinaryFiniteLinePullbackMap A N hA t f hY
        (ordinaryFiniteFirstChern A N hA Y hY M) =
      ordinaryFiniteFirstChern A N hA X hX (Scheme.Pic.map f M) := by
  exact ordinaryFiniteFirstChern_unique A N hA X hX (Scheme.Pic.map f M) _
    (ordinaryFiniteChern_pullback A N hA t f hY hX M _
      (ordinaryFiniteFirstChern_class A N hA Y hY M))

end AlgebraicGeometry.Etale
