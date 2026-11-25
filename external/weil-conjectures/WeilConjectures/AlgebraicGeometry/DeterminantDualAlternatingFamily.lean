/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.AlgebraicGeometry.DeterminantDualPairingFunctional
import WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt

/-! # Local alternating determinant functionals
Source: Stacks Project, Tags 0BRT and 03CY; Mathlib exterior-power determinant pairing.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

set_option backward.isDefEq.respectTransparency false in
/-- On a fixed open, the determinant pairing gives a unique alternating family of
internal functionals, characterized on wedges over every subopen.
Source: Stacks Project, Tag 0BRT, determinant inversion; Tag 03CY, module sheafification.
(blueprint: lem-sc-exterior-dual-pairing-local).

Proof: for a tuple of dual sections over U and each V mapping to U, evaluate these
sections on M(V). Compose the canonical exterior-power determinant pairing with
these evaluations. Naturality of internal Hom sections and preservation of the
finite determinant polynomial by ring restriction make this a presheaf morphism
on Over U. Extend uniquely through the sheafification of the exterior presheaf
on this open site. Restriction of sheafification to an open is sheafification
on that open site, so the resulting morphism is an internal dual section of
exteriorPower M n over U. The determinant is alternating and multilinear in
its columns; uniqueness of extension carries these identities to the internal
functional, giving the stated alternating map. For uniqueness, pure wedges
span each sectionwise exterior power, and the sheafification adjunction is
injective on morphisms into a sheaf. This includes n = 0 (empty determinant 1),
the empty open and the zero ring, without requiring local freeness. -/
theorem exterior_dual_pairing_local (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃! A : ((Scheme.Modules.dual M).val.obj (op U)) [⋀^Fin n]→ₗ[X.presheaf.obj (op U)]
        ((Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U)),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V))
        (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
        (A φ).app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det := by
  classical
  choose q hq huniq using exterior_dual_pairing_functional X M n U
  let A : ((Scheme.Modules.dual M).val.obj (op U)) [⋀^Fin n]→ₗ[X.presheaf.obj (op U)]
      ((Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U)) :=
    { toFun := q
      map_update_add' := by
        intro dec φ j x y
        cases Subsingleton.elim dec (instDecidableEqFin n)
        apply exteriorSheaf_dual_ext X M n U
        intro V g a
        change (q (Function.update φ j (x + y))).app (op (Over.mk g))
          (wedge (M := M) (r := n) (U := V) a) =
          ((q (Function.update φ j x)).app (op (Over.mk g))
            (wedge (M := M) (r := n) (U := V) a)) +
          ((q (Function.update φ j y)).app (op (Over.mk g))
            (wedge (M := M) (r := n) (U := V) a))
        rw [hq, hq, hq]
        let B : Matrix (Fin n) (Fin n) (X.presheaf.obj (op V)) :=
          Matrix.of fun i k ↦ (φ k).app (op (Over.mk g)) (a i)
        have hm (z : (Scheme.Modules.dual M).val.obj (op U)) :
            (Matrix.of fun i k ↦ (show X.presheaf.obj (op V) from
              (Function.update φ j z k).app (op (Over.mk g)) (a i))) =
              B.updateCol j (fun i ↦ z.app (op (Over.mk g)) (a i)) := by
          ext i k
          by_cases hk : k = j <;> simp [B, Matrix.updateCol, Function.update_apply, hk]
        rw [hm, hm, hm]
        have hadd : (fun i ↦ (show X.presheaf.obj (op V) from
            (x + y).app (op (Over.mk g)) (a i))) =
            (fun i ↦ (show X.presheaf.obj (op V) from x.app (op (Over.mk g)) (a i))) +
              (fun i ↦ (show X.presheaf.obj (op V) from y.app (op (Over.mk g)) (a i))) := rfl
        rw [hadd]
        exact Matrix.det_updateCol_add (R := X.presheaf.obj (op V)) B j
          (fun i ↦ (show X.presheaf.obj (op V) from x.app (op (Over.mk g)) (a i)))
          (fun i ↦ (show X.presheaf.obj (op V) from y.app (op (Over.mk g)) (a i)))
      map_update_smul' := by
        intro dec φ j r x
        cases Subsingleton.elim dec (instDecidableEqFin n)
        apply exteriorSheaf_dual_ext X M n U
        intro V g a
        change (q (Function.update φ j (r • x))).app (op (Over.mk g))
            (wedge (M := M) (r := n) (U := V) a) =
          (X.presheaf.map g.op r) * (show X.presheaf.obj (op V) from
            (q (Function.update φ j x)).app (op (Over.mk g))
              (wedge (M := M) (r := n) (U := V) a))
        rw [hq, hq]
        let B : Matrix (Fin n) (Fin n) (X.presheaf.obj (op V)) :=
          Matrix.of fun i k ↦ (φ k).app (op (Over.mk g)) (a i)
        have hm (z : (Scheme.Modules.dual M).val.obj (op U)) :
            (Matrix.of fun i k ↦ (show X.presheaf.obj (op V) from
              (Function.update φ j z k).app (op (Over.mk g)) (a i))) =
              B.updateCol j (fun i ↦ z.app (op (Over.mk g)) (a i)) := by
          ext i k
          by_cases hk : k = j <;> simp [B, Matrix.updateCol, Function.update_apply, hk]
        rw [hm, hm]
        have hs : (fun i ↦ (show X.presheaf.obj (op V) from
            (r • x).app (op (Over.mk g)) (a i))) =
            (X.presheaf.map g.op r) • (fun i ↦ (show X.presheaf.obj (op V) from
              x.app (op (Over.mk g)) (a i))) := rfl
        rw [hs]
        exact Matrix.det_updateCol_smul (R := X.presheaf.obj (op V)) B j
          (X.presheaf.map g.op r)
          (fun i ↦ (show X.presheaf.obj (op V) from x.app (op (Over.mk g)) (a i)))
      map_eq_zero_of_eq' := by
        intro φ i j hij hne
        apply exteriorSheaf_dual_ext X M n U
        intro V g a
        change (q φ).app (op (Over.mk g))
          (wedge (M := M) (r := n) (U := V) a) = 0
        rw [hq]
        exact Matrix.det_zero_of_column_eq (R := X.presheaf.obj (op V)) hne
          (fun k ↦ congrArg (fun z ↦ z.app (op (Over.mk g)) (a k)) hij) }
  refine ⟨A, ?_, ?_⟩
  · intro V g a φ
    exact hq φ V g a
  · intro B hB
    ext φ
    apply exteriorSheaf_dual_ext X M n U
    intro V g a
    exact (hB V g a φ).trans (hq φ V g a).symm


end AlgebraicGeometry
