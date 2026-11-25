/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import WeilConjectures.AlgebraicGeometry.DeterminantDualLocalFrames
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Local perfection of the exterior dual pairing
Source: Stacks Project, Tag 0BRT, determinant inversion.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

/-- A determinant-formula morphism is bijective on sections below an open on which M
is finite free, in every exterior degree.
Source: Stacks Project, Tag 0BRT, determinant pairing; Mathlib
`exteriorPower.basis_coord` and the finite dual basis.
(blueprint: lem-sc-exterior-dual-pairing-local-bijective).

Proof: restrict the given trivialization to each V contained in U. Sections of the
finite free sheaf and its internal dual become the free section module and its
ring-linear dual; the inverse to evaluation reconstructs a natural sheaf map by
basis coordinates. The wedge bases identify the exterior sheaves on these opens
with the sectionwise exterior powers: the latter are finite free sheaves, and
sheafification restricted to the open is characterized by the same adjunction.
Under these identifications the assumed formula identifies f on pure wedges with
Mathlib's pairingDual. Pure wedges span the sectionwise exterior powers, so the
maps agree everywhere. The wedge of each dual basis vector maps to the
corresponding coordinate functional (`exteriorPower.basis_coord`). Since the wedge
basis is finite, these functionals form its dual basis, proving bijectivity.
When n exceeds the rank, both exterior modules are zero;
when n=0 both are the ring. Zero rings and empty opens are allowed. -/
theorem exterior_dual_pairing_app_bijective (X : Scheme.{u}) (M : X.Modules) (n : ℕ)
    (f : Scheme.Modules.exteriorPower (Scheme.Modules.dual M) n ⟶
      Scheme.Modules.dual (Scheme.Modules.exteriorPower M n))
    (hf : ∀ (U : X.Opens) (a : Fin n → M.val.obj (op U))
      (φ : Fin n → (Scheme.Modules.dual M).val.obj (op U)),
      (f.val.app (op U) (wedge (M := Scheme.Modules.dual M) (r := n) (U := U) φ)).app
          (op (Over.mk (𝟙 U)))
        (wedge (M := M) (r := n) (U := U) a) =
      (Matrix.of fun i j ↦
        (show X.presheaf.obj (op U) from
          (φ j).app (op (Over.mk (𝟙 U))) (a i))).det)
    (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r)))
    (V : X.Opens) (g : V ⟶ U) :
    Function.Bijective (f.val.app (op V)) := by
  classical
  obtain ⟨a, φ, b, d, c, hφ, hb, hd, hc⟩ := exterior_dual_local_frames X M n U r e V g
  let targetBasis := d.dualBasis.map c.symm
  have hmap (s : Set.powersetCard (Fin r) n) : f.val.app (op V) (b s) = targetBasis s := by
    apply c.injective
    apply d.ext
    intro t
    have hdet : (Matrix.of fun i j ↦
        a.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
          (a (Set.powersetCard.ofFinEmbEquiv.symm t i))).det =
        d.dualBasis s (d t) := by
      rw [Module.Basis.dualBasis_apply_self]
      calc
        _ = exteriorPower.ιMultiDual (X.presheaf.obj (op V)) n a s
            (exteriorPower.ιMulti_family (X.presheaf.obj (op V)) n a t) := by
          rw [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
          rfl
        _ = (a.exteriorPower n).coord s ((a.exteriorPower n) t) := by
          rw [exteriorPower.basis_coord, exteriorPower.basis_apply]
        _ = _ := by
          rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    calc
      c (f.val.app (op V) (b s)) (d t) =
          (Matrix.of fun i j ↦
            a.coord (Set.powersetCard.ofFinEmbEquiv.symm s j)
              (a (Set.powersetCard.ofFinEmbEquiv.symm t i))).det := by
        rw [hc, hb, hd, hf]
        simp only [Function.comp_apply, hφ]
      _ = d.dualBasis s (d t) := hdet
      _ = c (targetBasis s) (d t) := by simp [targetBasis]
  have heq : (f.val.app (op V)).hom =
      (b.equiv targetBasis (Equiv.refl _)).toLinearMap := by
    apply b.ext
    intro s
    simpa using hmap s
  rw [show (f.val.app (op V) : _ → _) = b.equiv targetBasis (Equiv.refl _) by
    exact congrArg DFunLike.coe heq]
  exact (b.equiv targetBasis (Equiv.refl _)).bijective

end AlgebraicGeometry
