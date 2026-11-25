/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.AlgebraicGeometry.DeterminantDualAlternatingFamily
import WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt

/-! # Construction of the exterior dual pairing
Source: Stacks Project, Tag 0BRT, determinant inversion.
(blueprint: lem-sc-exterior-dual-pairing-construction).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

set_option backward.isDefEq.respectTransparency false in
/-- The determinant of evaluation defines a morphism of exterior sheaves, in every degree
and without any local freeness assumption.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.pairingDual_ιMulti_ιMulti`.
(blueprint: lem-sc-exterior-dual-pairing-construction).

Proof: for an open U and a tuple of internal dual sections, on each V contained in U
apply the determinant of their evaluations to tuples of M(V). This is alternating
and multilinear in both tuples, so the universal property of exterior powers gives
an exterior-power functional on every V. Evaluation is natural under restriction;
ring homomorphisms preserve the determinant. Thus these functionals form a morphism
from the exterior presheaf restricted to U to the structure sheaf restricted to U.
The sheafification adjunction extends it uniquely to the exterior sheaf. The same
uniqueness proves compatibility when U shrinks. Alternation in the dual tuple then
gives a map from the exterior presheaf of the internal dual to the internal dual of
the exterior sheaf, which is a sheaf. Sheafify again to obtain f. Both adjunction
units give exactly the displayed formula. Empty tuples give the determinant 1, and
all constructions work over the zero ring and on the empty open. -/
theorem exterior_dual_pairing_exists (X : Scheme.{u}) (M : X.Modules) (n : ℕ) :
    ∃ f :
    (Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n) ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M n),
    ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (wedge (M := Scheme.Modules.dual M) (r := n) (U := U) φ)).app
          (op (Over.mk (𝟙 U)))
        (wedge (M := M) (r := n) (U := U) a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det := by
  classical
  choose A hA huniq using exterior_dual_pairing_local X M n
  have hnat (U V : X.Opens) (g : V ⟶ U)
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
      A V (fun i ↦ (Scheme.Modules.dual M).val.map g.op (φ i)) =
        (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.map g.op (A U φ) := by
    apply exteriorSheaf_dual_ext X M n V
    intro W k a
    rw [hA V W k a]
    change _ = (A U φ).app (op (Over.mk (k ≫ g)))
      (wedge (M := M) (r := n) (U := W) a)
    rw [hA U W (k ≫ g) a]
    rfl
  have heval (U : X.Opens) (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
      exteriorPower.alternatingMapLinearEquiv (A U)
        (exteriorPower.ιMulti (X.presheaf.obj (op U)) n φ) = A U φ :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (A U) φ
  let p : (_root_.PresheafOfModules.exteriorPower (R := _) (Scheme.Modules.dual M).val n) ⟶
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val :=
    { app := fun U ↦ ModuleCat.ofHom
          (X := ((_root_.PresheafOfModules.exteriorPower (R := _)
            (Scheme.Modules.dual M).val n).obj U))
          (Y := (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj U)
          (exteriorPower.alternatingMapLinearEquiv (R := X.presheaf.obj (op U.unop))
            (N := (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U.unop))
            (A U.unop))
      naturality := by
        intro U V g
        rcases U with ⟨U₀⟩
        rcases V with ⟨V₀⟩
        apply ModuleCat.hom_ext
        apply exteriorPower.linearMap_ext (R := X.presheaf.obj (op U₀))
        ext φ
        change exteriorPower.alternatingMapLinearEquiv (A V₀)
            (((_root_.PresheafOfModules.exteriorPower (R := _) (Scheme.Modules.dual M).val n).map g)
              (exteriorPower.ιMulti (X.presheaf.obj (op U₀)) n φ)) =
          (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.map g
            (exteriorPower.alternatingMapLinearEquiv (A U₀)
              (exteriorPower.ιMulti (X.presheaf.obj (op U₀)) n φ))
        have hr := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _)
          (Scheme.Modules.dual M).val n g) φ
        change ((_root_.PresheafOfModules.exteriorPower (R := _)
            (Scheme.Modules.dual M).val n).map g)
          (exteriorPower.ιMulti (X.presheaf.obj (op U₀)) n φ) = _ at hr
        rw [hr]
        exact (heval V₀ _).trans ((hnat U₀ V₀ g.unop φ).trans
          (congrArg ((Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.map g)
            (heval U₀ φ).symm)) }
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)
  let f : Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M n) :=
    (adj.homEquiv _ _).symm p
  have hf := (adj.homEquiv
    ((_root_.PresheafOfModules.exteriorPower (R := _) (Scheme.Modules.dual M).val n))
    (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n))).apply_symm_apply p
  refine ⟨f, ?_⟩
  intro U a φ
  have h := congrArg
    (fun t ↦ t.app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n φ)) hf
  change f.val.app (op U)
      (wedge (M := Scheme.Modules.dual M) (r := n) (U := U) φ) =
    exteriorPower.alternatingMapLinearEquiv (A U)
      (exteriorPower.ιMulti (X.presheaf.obj (op U)) n φ) at h
  rw [heval U φ] at h
  rw [h]
  exact hA U U (𝟙 U) a φ


end AlgebraicGeometry
