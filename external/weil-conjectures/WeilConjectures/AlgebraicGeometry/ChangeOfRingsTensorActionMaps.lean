/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.ChangeOfRingsTensorActionMapsBalancing

/-! # Action and balancing maps for change of rings

Source: Stacks Project, Morphisms, proof of Lemma 01SB; Sheaves, Lemma 0089.
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a

/-- The two algebra actions and the canonical balancing map exist on sheaf tensors.
Source: Stacks Project, Morphisms, proof of Lemma 01SB (change of rings), and
Sheaves, Lemma 0089 (sheafification universal property).
(blueprint: lem-weil-pbc-change-of-rings-tensor-action-maps).

Proof: let K be the presheaf C tensor_O P. On each open, the maps
(b,c,p) ↦ c tensor bp and (b,c,p) ↦ φ(b)c tensor p are additive in all three
arguments and O-balanced. The equality φ(B.hom(r)) = C.hom(r), supplied by the
algebra morphism, proves balancing for the second map. Both commute with
restriction. Give K the B-action on P, respectively the B-action through φ on C.
Sheafify these B-module presheaves. Restriction of scalars preserves sheaves and
identifies each resulting O-module sheaf with the sheafification of K, by the
sheafification universal property. Thus both actions extend to S. Tensoring their
bilinear action maps and sheafifying gives a and d, with the stated formulas.
The sectionwise map C tensor_O P → C tensor_B P, c tensor p ↦ c tensor_B p,
is O-linear and natural. Compose with the change-of-rings sheafification unit
and extend to S to obtain g. The B-balanced tensor identity identifies the two
composites with g on each (b,c,p). Tensor generation and uniqueness in the two
successive sheafifications give a ≫ g = d ≫ g. No sections of a sheafification
are assumed to be global pure tensors; equality is checked through its unit.
-/
theorem exists_changeOfRings_tensor_action_maps (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let S := tensorObj C.toModule P₀
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    ∃ (a d : tensorObj B.toModule S ⟶ S) (g : S ⟶ T),
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        a.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) c (b • p)) ∧
      (∀ (W : Y.Opens) (b : B.right.obj.obj (op W))
          (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        d.app W (tmulSection (M := B.toModule) b
          (tmulSection (M := C.toModule) (N := P₀) c p)) =
          tmulSection (M := C.toModule) (N := P₀) (φ.right.hom.app (op W) b * c) p) ∧
      (∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app W (tmulSection (M := C.toModule) (N := P₀) c p) =
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
              (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p)) ∧
      a ≫ g = d ≫ g := by
  dsimp
  obtain ⟨a, d, g, h⟩ := exists_changeOfRings_tensor_action_maps_core Y B C φ P
  refine ⟨a, d, g, h.1, h.2.1, h.2.2, ?_⟩
  exact changeOfRings_tensor_action_comp_eq Y B C φ P a d g h

end AlgebraicGeometry.Scheme.Modules
