/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
import WeilConjectures.AlgebraicGeometry.ConstructibleStalkCardinalityBound
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Factorial.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.CurveCoefficientPair

/-- A constructible torsion sheaf on a curve is killed by a positive integer.
Source: Stacks Project, Definition 03RW and Lemma 095E; the finite-bound
argument in step 1 of the parent constructible subobject node, used for 09BH (2).

Proof: the curve is Noetherian because it is quasi-compact and of finite type over
its base field. Apply the uniform finite geometric stalk-cardinality bound to obtain N.
Choose N factorial, which is positive even for N = 0. Each abelian stalk is nonempty
and finite, so its positive cardinality divides N factorial. Lagrange's theorem then
shows that N factorial annihilates every stalk element. Additivity of the stalk functor
identifies this with the stalk map of N factorial times the identity. Joint faithfulness
of the algebraic-closure residue-field stalks proves that this morphism is zero.
The geometric cardinality bound is the remaining named theorem; the finite-group
argument and the passage back to sheaf morphisms are proved here.
(blueprint: lem-weil-pbc-curve-constructible-annihilator) -/
theorem exists_annihilator_of_constructible {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k) (hF : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))) :
    ∃ n : ℕ, 0 < n ∧ n • 𝟙 P.F = 0 := by
  have : IsCurve P.toSpec := P.isCurve
  have : CompactSpace P.C := QuasiCompact.compactSpace_of_compactSpace P.toSpec
  have : IsNoetherian P.C := { __ := LocallyOfFiniteType.isLocallyNoetherian P.toSpec }
  obtain ⟨N, hN⟩ := Scheme.exists_stalk_cardinality_bound_of_constructible P.C P.F hF
  refine ⟨N.factorial, Nat.factorial_pos N, ?_⟩
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let Φ := Scheme.pointSmallEtale (P.C.algClosurePoint x)
  have : (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).Additive := Φ.sheafFiber_additive
  let G := (Φ.sheafFiber (A := AddCommGrpCat.{u + 1})).obj P.F
  have : Finite G := (hN x).1
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨m, hm⟩ := Nat.dvd_factorial (Nat.card_pos (α := G)) (hN x).2
  change N.factorial • a = 0
  rw [hm, mul_nsmul, card_nsmul_eq_zero', nsmul_zero]

end AlgebraicGeometry.CurveCoefficientPair
