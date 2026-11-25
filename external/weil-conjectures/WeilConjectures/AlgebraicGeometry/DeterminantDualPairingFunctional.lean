/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.AlgebraicGeometry.ExteriorSheafDualExt
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # An internal determinant functional for a fixed tuple
Source: Stacks Project, Tags 0BRT and 03CY.
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

-- Explicit scalar restrictions on the over-open site require additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- A tuple of dual sections determines a unique internal functional on the exterior sheaf.
Source: Stacks Project, Tag 0BRT, determinant pairing; Tag 03CY, module sheafification.
(blueprint: lem-sc-exterior-dual-pairing-functional).

Proof: on each subopen V of U, evaluate the given dual sections on M(V) and
apply Mathlib's exterior-power determinant pairing. This gives a linear map
from the exterior power of M(V) to O(V). Naturality holds on pure wedges,
because the dual sections commute with restrictions and ring maps preserve
the determinant polynomial; pure wedges span, so it holds everywhere.
These maps form a morphism of module presheaves on Over U. Restrict the
exterior sheafification unit to this open site. It is locally bijective,
since its underlying abelian-presheaf map is the sheafification unit and
open restriction preserves local bijectivity. The structure sheaf restricted
to Over U is a sheaf. Thus the presheaf morphism extends uniquely across
the unit, giving q and the claimed formula. Uniqueness follows by agreement
on spanning pure wedges before extension. This construction works for n = 0,
empty opens and zero rings. -/
theorem exterior_dual_pairing_functional (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (U : X.Opens) (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)) :
    ∃! q : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U),
      ∀ (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)),
        q.app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
          (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
            (φ j).app (op (Over.mk g)) (a i))).det := by
  classical
  let P := (_root_.PresheafOfModules.exteriorPower (R := X.presheaf) M.val n)
  let N := (SheafOfModules.unit X.ringCatSheaf).val
  let F := PresheafOfModules.restrictOver X.sheaf.obj U
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app P
  let ψ (W : (Over U)ᵒᵖ) :
      Module.Dual (X.presheaf.obj (op W.unop.left))
        (⋀[X.presheaf.obj (op W.unop.left)]^n (M.val.obj (op W.unop.left))) :=
    exteriorPower.alternatingMapToDual _ _ n
      (fun j ↦ ((φ j).app W).hom)
  have hψ (W : (Over U)ᵒᵖ) (a : Fin n → M.val.obj (op W.unop.left)) :
      ψ W (exteriorPower.ιMulti (X.presheaf.obj (op W.unop.left)) n a) =
        (Matrix.of fun i j ↦ (show X.presheaf.obj (op W.unop.left) from
          (φ j).app W (a i))).det :=
    exteriorPower.alternatingMapToDual_apply_ιMulti
      (R := X.presheaf.obj (op W.unop.left)) (fun j ↦ ((φ j).app W).hom) a
  let p : F.obj P ⟶ F.obj N :=
    { app := fun W ↦ ModuleCat.ofHom (ψ W)
      naturality := by
        intro W Z g
        apply ModuleCat.hom_ext
        apply exteriorPower.linearMap_ext (R := X.presheaf.obj (op W.unop.left))
        ext a
        change ψ Z (P.map g.unop.left.op
            (exteriorPower.ιMulti (X.presheaf.obj (op W.unop.left)) n a)) =
          N.map g.unop.left.op
            (ψ W (exteriorPower.ιMulti (X.presheaf.obj (op W.unop.left)) n a))
        erw [_root_.PresheafOfModules.exteriorPower_map_ιMulti]
        have hz := hψ Z (fun i ↦ M.val.map g.unop.left.op (a i))
        have hw := hψ W a
        refine hz.trans ?_
        refine Eq.trans ?_ (congrArg (N.map g.unop.left.op) hw.symm)
        change (Matrix.of fun i j ↦
          (show X.presheaf.obj (op Z.unop.left) from
            (φ j).app Z (M.val.map g.unop.left.op (a i)))).det =
          (X.presheaf.map g.unop.left.op)
            ((Matrix.of fun i j ↦
              (show X.presheaf.obj (op W.unop.left) from (φ j).app W (a i))).det)
        rw [RingHom.map_det]
        congr 1
        ext i j
        exact PresheafOfModules.naturality_apply (φ j) g (a i) }
  let e := (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map η
  have hi : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e := by
    change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify _ P.presheaf)
    infer_instance
  have hs : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify _ P.presheaf)
    infer_instance
  have hi' : PresheafOfModules.IsLocallyInjective
      ((Opens.grothendieckTopology X).over U) (F.map η) :=
    Presheaf.isLocallyInjective_whisker ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) (Over.forget U) e
  have hs' : PresheafOfModules.IsLocallySurjective
      ((Opens.grothendieckTopology X).over U) (F.map η) :=
    Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology X).over U)
      (Opens.grothendieckTopology X) (Over.forget U) e
  have hN : Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      (F.obj N).presheaf :=
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (SheafOfModules.unit X.ringCatSheaf)).over U |>.property
  let eqv := PresheafOfModules.homEquivOfIsLocallyBijective (F.map η) hN
  let q : (Scheme.Modules.dual (Scheme.Modules.exteriorPower M n)).val.obj (op U) :=
    eqv.symm p
  have hq : F.map η ≫ q = p := eqv.apply_symm_apply p
  have hformula (V : X.Opens) (g : V ⟶ U) (a : Fin n → M.val.obj (op V)) :
      q.app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
        (Matrix.of fun i j ↦ (show X.presheaf.obj (op V) from
          (φ j).app (op (Over.mk g)) (a i))).det := by
    have h := CategoryTheory.congr_fun (congrArg
      (fun t ↦ t.app (op (Over.mk g))) hq)
      (exteriorPower.ιMulti (X.presheaf.obj (op V)) n a)
    change q.app (op (Over.mk g)) (wedge (M := M) (r := n) (U := V) a) =
      ψ (op (Over.mk g)) (exteriorPower.ιMulti (X.presheaf.obj (op V)) n a) at h
    refine h.trans ?_
    exact exteriorPower.alternatingMapToDual_apply_ιMulti
      (R := X.presheaf.obj (op V)) (fun j ↦ ((φ j).app (op (Over.mk g))).hom) a
  refine ⟨q, hformula, ?_⟩
  intro r hr
  exact (exteriorSheaf_dual_ext X M n U q r (fun V g a ↦
    (hformula V g a).trans (hr V g a).symm)).symm

end AlgebraicGeometry
