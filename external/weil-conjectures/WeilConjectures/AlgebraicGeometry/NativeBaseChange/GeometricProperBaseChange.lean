/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Native.NativeBaseChangeOpenChart
import WeilConjectures.AlgebraicGeometry.Native.NativeAffineProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.Adic.MayerVietoris
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The geometric native derived proper base-change mate
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace NativeBaseChange

attribute [local irreducible] DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]

/-- Base change of a map to the fixed algebraic closure. -/
abbrev geometricMap {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y)
    [f.IsOver (Spec (CommRingCat.of k₀))] :=
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

variable {Z' Z T' T : Scheme.{u}}
  [Z'.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  [T'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {v : Z' ⟶ Z} {p' : Z' ⟶ T'} {p : Z ⟶ T} {g : T' ⟶ T}
  [v.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
  [p.IsOver (Spec (CommRingCat.of k₀))] [g.IsOver (Spec (CommRingCat.of k₀))]

omit [Finite k₀] in
/-- The commutative geometric square, without imposing Cartesian hypotheses. -/
theorem geometricSquare (sq : CommSq v p' p g) :
    CommSq (geometricMap k₀ v) (geometricMap k₀ p')
      (geometricMap k₀ p) (geometricMap k₀ g) := by
  constructor
  dsimp only [geometricMap]
  rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
  congr 1
  exact sq.w

omit [Finite k₀] in
private theorem geometricSquare_isPullback (sq : ChosenCartesianSquare v p' p g) :
    IsPullback (geometricMap k₀ v) (geometricMap k₀ p')
      (geometricMap k₀ p) (geometricMap k₀ g) := by
  have hs : IsPullback v p' p g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hb := ((hs.asOver (Spec (CommRingCat.of k₀))).map
    (Over.pullback (Scheme.specAlgebraicClosure k₀).hom)).map
      (Over.forget (Spec (CommRingCat.of (AlgebraicClosure k₀))))
  simpa [geometricMap, Scheme.Hom.geometricFiberMap, Scheme.Hom.geometricFiber,
    Over.pullback, pullback.map, OverClass.asOver, CategoryTheory.over] using hb

private theorem affineChart_descent
    (k : Type u) [Field k] [Algebra k₀ k] [IsAlgClosure k₀ k]
    [Fact (ringChar k₀ ≠ l)]
    {X' X Y' Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k))]
    [Y'.Over (Spec (CommRingCat.of k))]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [g.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k))]
    (sq : IsPullback v p' p g) (M : DerivedCategory (ProEtale.AdicSheaf l X))
    (hM : DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((ProEtale.adicDerivedBaseChange l sq.toCommSq).app M) := by
  let U := Y.affineCover.pullback₁ g
  let C := U.bind fun a ↦ (U.X a).affineCover
  apply ProEtale.isIso_of_isIso_mapDerivedCategory_adicUpperStar l C.f
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _ C.mem₀)
  rintro ⟨a, b⟩
  change Y.affineCover.I₀ at a
  change (pullback g (Y.affineCover.f a)).affineCover.I₀ at b
  let A := Y.affineCover.X a
  let i := Y.affineCover.f a
  let V := (pullback g i).affineCover
  let B := V.X b
  let j := V.f b ≫ pullback.fst g i
  let h := V.f b ≫ pullback.snd g i
  have w : h ≫ i = j ≫ g := by
    dsimp only [h, j]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  let S := Spec (CommRingCat.of k)
  let : A.Over S := ⟨i ≫ (Y ↘ S)⟩
  let : B.Over S := ⟨j ≫ (Y' ↘ S)⟩
  let : (pullback p i).Over S := ⟨pullback.snd p i ≫ (A ↘ S)⟩
  let : (pullback (pullback.snd p i) h).Over S :=
    ⟨pullback.snd (pullback.snd p i) h ≫ (B ↘ S)⟩
  have : h.IsOver S := ⟨by
    change h ≫ (i ≫ (Y ↘ S)) = j ≫ (Y' ↘ S)
    rw [← Category.assoc, w, Category.assoc, comp_over g S]⟩
  have : (pullback.snd p i).IsOver S := ⟨rfl⟩
  have : (pullback.snd (pullback.snd p i) h).IsOver S := ⟨rfl⟩
  have : (pullback.fst (pullback.snd p i) h).IsOver S := ⟨by
    change pullback.fst _ _ ≫ (pullback.snd p i ≫ (A ↘ S)) =
      pullback.snd _ _ ≫ (B ↘ S)
    rw [← Category.assoc, pullback.condition, Category.assoc, comp_over h S]⟩
  have : IsAffine A := inferInstanceAs (IsAffine (Y.affineCover.X a))
  have : IsAffine B := inferInstanceAs (IsAffine (V.X b))
  have : LocallyOfFiniteType (A ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ (Y ↘ S)))
  have : LocallyOfFiniteType (B ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ (Y' ↘ S)))
  let R := ProEtale.adicUpperStar l (pullback.fst p i)
  have hR : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((DerivedCategory.homologyFunctor _ n).obj (R.mapDerivedCategory.obj M)) := by
    intro n
    exact ProEtale.IsAdicConstructibleSheaf.of_iso
      ((R.mapDerivedCategoryHomologyFunctorIso n).app M)
      ((hc n).upperStar (pullback.fst p i))
  have hl := ProEtale.adicDerivedBaseChange_isIso_of_affine k₀ k l
    (IsPullback.of_hasPullback (pullback.snd p i) h) (R.mapDerivedCategory.obj M)
    (R.bounded_mapDerivedCategory_obj hM) hR
  obtain ⟨e⟩ := ProEtale.adicDerivedBaseChange_openChart l sq i j h w M
  exact (Arrow.isIso_iff_isIso_of_isIso e.hom).mpr hl

/-- Invertibility of the geometric mate on bounded constructible native modules. -/
theorem geometric_proper_baseChange_isIso [Fact (ringChar k₀ ≠ l)]
    (sq : ChosenCartesianSquare v p' p g) [IsProper p]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (T' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of k₀))]
    (M : _root_.DerivedCategory
      (ProEtale.AdicSheaf l (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hM : _root_.DerivedCategory.TStructure.t.bounded M)
    (hc : ∀ n : ℤ, ProEtale.IsAdicConstructibleSheaf
      ((_root_.DerivedCategory.homologyFunctor _ n).obj M)) :
    IsIso ((ProEtale.adicDerivedBaseChange l (geometricSquare k₀ sq.toCommSq)).app M) := by
  let S := Spec (CommRingCat.of (AlgebraicClosure k₀))
  let : (T ↘ Spec (CommRingCat.of k₀)).geometricFiber.Over S :=
    ⟨(T ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  let : (T' ↘ Spec (CommRingCat.of k₀)).geometricFiber.Over S :=
    ⟨(T' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure⟩
  have : LocallyOfFiniteType ((T ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType
      (T ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  have : LocallyOfFiniteType ((T' ↘ Spec (CommRingCat.of k₀)).geometricFiber ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType
      (T' ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  have : (geometricMap k₀ g).IsOver S :=
    ⟨Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure _ _⟩
  have : IsProper (geometricMap k₀ p) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) p
      (comp_over p (Spec (CommRingCat.of k₀))) inferInstance
  exact affineChart_descent k₀ l (AlgebraicClosure k₀)
    (geometricSquare_isPullback k₀ sq) M hM hc

end NativeBaseChange

end AlgebraicGeometry
