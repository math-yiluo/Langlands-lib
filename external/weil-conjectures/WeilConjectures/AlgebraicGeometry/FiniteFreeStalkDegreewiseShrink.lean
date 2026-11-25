/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkRestrictionComplexIso
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeStalkFiniteEquations
import WeilConjectures.AlgebraicGeometry.StalkRestrictionSubopenCompatibility
import Mathlib.Data.Int.Interval

/-! # Shrinking differential-commutativity defects

Source: lem-pc-finite-free-stalk-chain-map-lift-local, the zero-germ shrinking step.
(blueprint: lem-pc-finite-free-stalk-degreewise-shrink)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- An already defined degreewise family whose stalk commutes with differentials
can be restricted to a smaller neighbourhood where it commutes.

Source: lem-pc-finite-free-stalk-chain-map-lift-local, step 2 (vanishing of the
commutativity defects) and step 3 (compatibility of stalk restriction), expanding
lemma-coherent-base-change-invertible-sheaves--3's extension of the finite calculation.

Proof: In the restricted finite bases form, for every adjacent degree, the matrix
of g n followed by d_Q minus d_P followed by g (n+1). Its pullback to the stalk
scheme is zero by hcomm. Thus its entries have zero germ at y. Only degrees for
which both P.X n and Q.X (n+1) are nonzero need checking; boundedness makes this
list finite. For every entry the germ equality criterion gives a neighbourhood
inside U on which the entry vanishes. Intersect this finite collection to obtain
V containing y, with V <= U. Restrict every g n to V and transport along the
canonical comparison between direct restriction to V and restriction through U;
call the resulting family k. All adjacent chain equations now hold. Outside the
finite list either the source or target is zero, and the equation is automatic.
Restriction transitivity and pullback composition identify the stalk of k n with
the stalk of g n conjugated by the comparisons through Y. This is the displayed
component formula, with the inverse comparison at U followed by the one at V.
The compatibility follows by the associativity of pullback composition and the
identity of the composite maps from Spec O_{Y,y}. For an empty support interval,
rank-zero terms, or an already commuting family, the same construction works
with no equations or no further shrinking. The lemma extends no prescribed map:
it starts with the family g already defined on U.
(blueprint: lem-pc-finite-free-stalk-degreewise-shrink) -/
theorem exists_shrink_degreewise_comm_of_stalk
    {Y : Scheme.{u}} (P Q : CochainComplex Y.Modules ℤ)
    (a b c e : ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hQc : Q.IsStrictlyGE c) (hQe : Q.IsStrictlyLE e)
    (hPfree : ∀ n : ℤ, IsZero (P.X n) ∨ ∃ s : ℕ, Nonempty
      (P.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (hQfree : ∀ n : ℤ, IsZero (Q.X n) ∨ ∃ s : ℕ, Nonempty
      (Q.X n ≅ SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin s))))
    (y : Y) (U : Y.Opens) (hyU : y ∈ U)
    (g : ∀ n : ℤ,
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n)
    (hcomm : ∀ n : ℤ,
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) ≫
        (((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)).d
            n (n + 1) =
      (((Modules.pullback (U.fromSpecStalkOfMem y hyU)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).d
          n (n + 1) ≫ (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g (n + 1))) :
    ∃ (V : Y.Opens), ∃ (hyV : y ∈ V), V ≤ U ∧ ∃ (k : ∀ n : ℤ,
      (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n ⟶
      (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).X n),
      (∀ n : ℤ, k n ≫
        (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj Q).d
          n (n + 1) =
        (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).d
          n (n + 1) ≫ k (n + 1)) ∧
      (∀ n : ℤ, (Modules.pullback (V.fromSpecStalkOfMem y hyV)).map (k n) =
        ((stalkRestrictionComplexIso V y hyV).app P).hom.f n ≫
        ((stalkRestrictionComplexIso U y hyU).app P).inv.f n ≫
        (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (g n) ≫
        ((stalkRestrictionComplexIso U y hyU).app Q).hom.f n ≫
        ((stalkRestrictionComplexIso V y hyV).app Q).inv.f n) := by
  classical
  let I := ↥(Finset.Icc (max a (c - 1)) (min b (e - 1)))
  let R := (restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)
  let f : ∀ i : I, (restrictFunctor U.ι).obj (P.X i.val) ⟶
      (restrictFunctor U.ι).obj (Q.X (i.val + 1)) :=
    fun i => g i.val ≫ (R.obj Q).d i.val (i.val + 1)
  let t : ∀ i : I, (restrictFunctor U.ι).obj (P.X i.val) ⟶
      (restrictFunctor U.ι).obj (Q.X (i.val + 1)) :=
    fun i => (R.obj P).d i.val (i.val + 1) ≫ g (i.val + 1)
  have hft : ∀ i : I,
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (f i) =
      (Modules.pullback (U.fromSpecStalkOfMem y hyU)).map (t i) := by
    intro i
    simpa only [f, t, R, Functor.map_comp, Functor.mapHomologicalComplex_obj_d]
      using hcomm i.val
  obtain ⟨V, hyV, hVU, hV⟩ := exists_shrink_finite_free_map_eq
    (fun i : I => P.X i.val) (fun i : I => Q.X (i.val + 1))
    (fun i => hPfree i.val) (fun i => hQfree (i.val + 1)) y U hyU f t hft
  let T := restrictFunctor (Y.homOfLE hVU)
  let C := NatIso.mapHomologicalComplex
    ((restrictFunctorCongr (Y.homOfLE_ι hVU)).symm ≪≫
      restrictFunctorComp (Y.homOfLE hVU) U.ι) (ComplexShape.up ℤ)
  let k := fun n : ℤ => (C.app P).hom.f n ≫ T.map (g n) ≫ (C.app Q).inv.f n
  refine ⟨V, hyV, hVU, k, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ Finset.Icc (max a (c - 1)) (min b (e - 1))
    · have heq := hV ⟨n, hn⟩
      have hc := congrArg
        (fun z => (C.app P).hom.f n ≫ z ≫ (C.app Q).inv.f (n + 1)) heq
      dsimp [f, t] at hc
      simp only [Functor.map_comp, Category.assoc] at hc
      have hQ := (C.app Q).inv.comm n (n + 1)
      have hP := (C.app P).hom.comm n (n + 1)
      simp only [Functor.mapHomologicalComplex_obj_d, Functor.comp_map] at hQ hP
      dsimp only [k]
      simp only [Functor.mapHomologicalComplex_obj_d, Category.assoc]
      rw [hQ]
      simp only [R, Functor.mapHomologicalComplex_obj_d] at hc
      exact hc.trans (by
        simpa only [T, Category.assoc, Iso.app_hom, Iso.app_inv] using congrArg
          (fun z => z ≫ T.map (g (n + 1)) ≫ (C.app Q).inv.f (n + 1)) hP)
    · have hn' : n < a ∨ b < n ∨ n + 1 < c ∨ e < n + 1 := by
        simp only [Finset.mem_Icc, max_le_iff, le_min_iff] at hn
        omega
      rcases hn' with hn' | hn' | hn' | hn'
      · exact ((restrictFunctor V.ι).map_isZero
          (P.isZero_of_isStrictlyGE a n hn')).eq_of_src _ _
      · exact ((restrictFunctor V.ι).map_isZero
          (P.isZero_of_isStrictlyLE b n hn')).eq_of_src _ _
      · exact ((restrictFunctor V.ι).map_isZero
          (Q.isZero_of_isStrictlyGE c (n + 1) hn')).eq_of_tgt _ _
      · exact ((restrictFunctor V.ι).map_isZero
          (Q.isZero_of_isStrictlyLE e (n + 1) hn')).eq_of_tgt _ _
  · intro n
    exact stalkRestrictionComplexIso_map_subopen P Q y U V hyU hyV hVU n (g n)

end AlgebraicGeometry.Scheme.Modules
