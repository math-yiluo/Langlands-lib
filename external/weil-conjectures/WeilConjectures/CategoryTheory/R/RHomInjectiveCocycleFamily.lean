/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! A compatible family of cocycle maps on injective complexes. -/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- Additive cocycle comparisons on injective complexes, with their normalization
and compatibility with chain maps.
Source: Stacks Tags 06XR (1) and 070I; the two parts of the natural-map construction.
(blueprint: def-sc-p1-rhom-injective-cocycle-family). -/
structure RhomInjectiveCocycleFamily
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}]
    (M : C) where
  map : ∀ (I : CochainComplex.Plus C) (_hi : ∀ k : ℤ, Injective (I.obj.X k))
      (n : ℤ),
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    (H n).obj (RV.obj ((DerivedCategory.Plus.Q (C := C)).obj I)) →+
      (S ⟶ ((DerivedCategory.Plus.Q (C := C)).obj I).obj⟦n⟧)

  normalize :
    let V := preadditiveCoyoneda.obj (op M)
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    ∀ (I : CochainComplex.Plus C) (hi : ∀ k : ℤ, Injective (I.obj.X k))
        (n : ℤ) (f : M ⟶ I.obj.X n) (hf : f ≫ I.obj.d n (n + 1) = 0),
      let J := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
      let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
        ⟨f, by
          change f ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0
          rw [CochainComplex.next]
          exact hf⟩)
      let b := (DerivedCategory.Plus.homologyFunctorObjQIso
        (V.mapCochainComplexPlus.obj I) n).inv a
      let η := V.rightDerivedFunctorPlusUnit.app I
      map I hi n ((H n).map η b) =
        ShiftedHom.map (Cocycle.equivHomShift.symm
            (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
          ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧'
  natural :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    ∀ (I J : CochainComplex.Plus C)
        (hi : ∀ k : ℤ, Injective (I.obj.X k))
        (hj : ∀ k : ℤ, Injective (J.obj.X k)) (n : ℤ)
        (φ : I.obj ⟶ J.obj)
        (a : (H n).obj (RV.obj ((DerivedCategory.Plus.Q (C := C)).obj I))),
      map J hj n ((H n).map (RV.map
        ((DerivedCategory.Plus.Q (C := C)).map (ObjectProperty.homMk φ))) a) =
        map I hi n a ≫
          ((DerivedCategory.Plus.ι (C := C)).map
            ((DerivedCategory.Plus.Q (C := C)).map (ObjectProperty.homMk φ)))⟦n⟧'

end CategoryTheory.Functor
