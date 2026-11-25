/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkDegreewiseLiftAux
import Mathlib.Data.Int.Interval
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite intersection combines degreewise local representatives into one neighbourhood.
(blueprint: lem-pc-finite-free-stalk-degreewise-lift-core) -/
theorem exists_degreewise_of_stalk_local_core
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (y : Y)
    (t : ∀ n : ℤ,
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj P).X n ⟶
      (((Modules.pullback (Y.fromSpecStalk y)).mapHomologicalComplex _).obj Q).X n)
    (hlocal : ∀ n : ℤ, ∃ (U : Y.Opens), ∃ (hyU : y ∈ U), ∃ (g :
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
        ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
          ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n) :
    ∃ (U : Y.Opens), ∃ (hyU : y ∈ U),
      ∀ n : ℤ, ∃ (g :
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map g =
          ((stalkRestrictionComplexIso U y hyU).app P).hom.f n ≫ t n ≫
            ((stalkRestrictionComplexIso U y hyU).app Q).inv.f n   := by
  classical
  let I := Finset.Icc (max a c) (min b e)
  apply exists_degreewise_finite_aux P Q y t I
  · intro n hn
    exact hlocal n
  · intro n hn
    refine ⟨0, ?_⟩
    have hout : n < a ∨ b < n ∨ n < c ∨ e < n := by
      dsimp [I] at hn
      simp only [Finset.mem_Icc] at hn
      omega
    rcases hout with h | h | h | h
    · have hz := P.isZero_of_isStrictlyGE a n h
      exact ((pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map_isZero
        ((restrictFunctor (⊤ : Y.Opens).ι).map_isZero hz)).eq_of_src _ _
    · have hz := P.isZero_of_isStrictlyLE b n h
      exact ((pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map_isZero
        ((restrictFunctor (⊤ : Y.Opens).ι).map_isZero hz)).eq_of_src _ _
    · have hz := Q.isZero_of_isStrictlyGE c n h
      exact ((pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map_isZero
        ((restrictFunctor (⊤ : Y.Opens).ι).map_isZero hz)).eq_of_tgt _ _
    · have hz := Q.isZero_of_isStrictlyLE e n h
      exact ((pullback ((⊤ : Y.Opens).fromSpecStalkOfMem y (by simp))).map_isZero
        ((restrictFunctor (⊤ : Y.Opens).ι).map_isZero hz)).eq_of_tgt _ _
end AlgebraicGeometry.Scheme.Modules
