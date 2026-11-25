/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

/-- A lifted finite matrix presents a quotient whose scalar extension is the
quotient by the corresponding colimit matrix.

Source: Stacks Project, Algebra, Tag 05N7, proof of (1).
(blueprint: lem-pc-finite-relation-quotient-comparison).

Proof: put R = F.obj i, A = colimit F, and let R act on A through the
coprojection. The sequence R^m --qi--> R^n --> R^n / range qi --> 0 is
right exact by the definition of the quotient. Tensoring it with A over R
preserves right exactness, so its last term is the cokernel of A tensor qi.
For each finite free module the map a tensor x to (a * image(x_j))_j is an
A-linear equivalence, with inverse sending y to the sum of y_j tensor e_j.
Under these equivalences A tensor qi agrees with q: the coefficient hypothesis
identifies their values on each standard basis vector, hence on every vector
by linearity. Their cokernels are therefore A-linearly isomorphic. Finally,
ULift.down is a linear equivalence; its scalar extension and the inverse
ULift equivalence on the output transport this cokernel isomorphism to the
specified module universes. Empty bases have empty sums and give the same
argument for n = 0 or m = 0. No flatness is needed. -/
theorem finite_relation_quotient_comparison
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (n m : ℕ)
    (q : (Fin m → (colimit F : CommRingCat)) →ₗ[(colimit F : CommRingCat)]
      (Fin n → (colimit F : CommRingCat)))
    (i : I) (qi : (Fin m → F.obj i) →ₗ[F.obj i] (Fin n → F.obj i))
    (hcoeff : ∀ (j : Fin n) (k : Fin m),
      (colimit.ι F i).hom (qi (Pi.single k 1) j) = q (Pi.single k 1) j) :
    Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj
        (ModuleCat.of (F.obj i) (ULift.{v} ((Fin n → F.obj i) ⧸ LinearMap.range qi))) ≅
        ModuleCat.of (colimit F : CommRingCat)
          (ULift.{v} ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q))) := by
  classical
  let R := F.obj i
  let S := (colimit F : CommRingCat)
  let f : R →+* S := (colimit.ι F i).hom
  let := f.toAlgebra
  let en := TensorProduct.piScalarRight R S S (Fin n)
  let em := TensorProduct.piScalarRight R S S (Fin m)
  have hcoord (x : Fin m → R) (j : Fin n) :
      f (qi x j) = q (fun k ↦ f (x k)) j := by
    have hx : x = ∑ k : Fin m, x k • Pi.single k (1 : R) := by
      ext k
      simp [Pi.single_apply]
    have hy : (fun k ↦ f (x k)) = ∑ k : Fin m, f (x k) • Pi.single k (1 : S) := by
      ext k
      simp [Pi.single_apply]
    have hqi : qi x = ∑ k : Fin m, x k • qi (Pi.single k 1) := by
      conv_lhs => rw [hx]
      simp only [map_sum, map_smul]
    rw [hqi, hy]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      LinearMap.map_smul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show f (qi (Pi.single k 1) j) = q (Pi.single k 1) j from hcoeff j k]
  have hmatrix : en.toLinearMap ∘ₗ qi.baseChange S = q ∘ₗ em.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    ext j
    change en (a ⊗ₜ[R] qi x) j = q (em (a ⊗ₜ[R] x)) j
    simp only [en, em, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul]
    change f (qi x j) * a = q (fun k ↦ f (x k) * a) j
    have hy : (fun k ↦ f (x k) * a) = a • (fun k ↦ f (x k)) := by
      ext k
      simp [mul_comm]
    rw [hy, map_smul, Pi.smul_apply, smul_eq_mul, hcoord]
    exact mul_comm _ _
  have hrange : LinearMap.range (qi.baseChange S) =
      LinearMap.range ((LinearMap.range qi).subtype.baseChange S) := by
    have hf : qi = (LinearMap.range qi).subtype ∘ₗ qi.rangeRestrict := rfl
    nth_rewrite 1 [hf]
    rw [LinearMap.baseChange_comp]
    apply LinearMap.range_comp_of_range_eq_top
    apply LinearMap.range_eq_top.mpr
    exact LinearMap.baseChange_surjective S qi.surjective_rangeRestrict
  have hmap : (LinearMap.range ((LinearMap.range qi).subtype.baseChange S)).map
      en.toLinearMap = LinearMap.range q := by
    rw [← hrange, ← LinearMap.range_comp, hmatrix]
    exact LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr em.surjective)
  let eqt := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := R) S R S
    (LinearMap.range qi)
  let eqf := Submodule.Quotient.equiv _ _ en hmap
  let eu := (ULift.moduleEquiv : ULift.{v} ((Fin n → R) ⧸ LinearMap.range qi) ≃ₗ[R]
    ((Fin n → R) ⧸ LinearMap.range qi)).baseChange R S _ _
  let e := eu.trans (eqt.trans (eqf.trans ULift.moduleEquiv.symm))
  exact ⟨e.toModuleIso⟩

end ModuleCat
