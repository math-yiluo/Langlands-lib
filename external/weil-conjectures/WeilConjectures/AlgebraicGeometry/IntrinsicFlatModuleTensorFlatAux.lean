/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Flat affine sections give flat stalks

Source: Stacks Project, Tag 01U4, implication (2) to (1).
(blueprint: lem-pc-intrinsic-flat-module-flat-stalk).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Flat affine sections of a quasi-coherent module give flat modules at every stalk.
Source: Stacks Project, Tag 01U4, implication (2) to (1), with the identity morphism.
(blueprint: lem-pc-intrinsic-flat-module-flat-stalk).

Proof: Fix a point x and an affine open neighbourhood V of x. The identity's map
on sections of V is the identity, so the hypothesis gives flatness of G(V) over O(V).
Quasi-coherence identifies the stalk G_x with the localization of G(V) at the prime
of O(V) corresponding to x, and identifies O_x with the localization of O(V) at
that prime, with the same scalar action. Localization is extension of scalars to
O_x and preserves flatness. Transport along these module and ring identifications
gives the asserted flatness. The empty scheme has no points to check; zero modules
and the zero ring introduce no exception. -/
theorem flat_stalk_of_affine_sections_flat {Y : Scheme.{u}} (G : Y.Modules)
    [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : ∀ V : Y.affineOpens,
      letI : Module Γ(Y, V.1) Γ(G, V.1) :=
        Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom
      Module.Flat (Γ(Y, V.1)) (Γ(G, V.1))) (x : Y) :
    Module.Flat (Y.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj G) := by
  obtain ⟨U, hU, hx, _⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) (by trivial)
  let V : Y.affineOpens := ⟨U, hU⟩
  let : Module Γ(Y, V.1) Γ(G, V.1) :=
    Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V.1 V.1 (le_rfl)).hom
  let : Algebra Γ(Y, V.1) (Y.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨x, hx⟩
  have : Module.Flat Γ(Y, V.1) Γ(G, V.1) := hflat V
  have : Module.Flat (Y.presheaf.stalk x)
      (TensorProduct Γ(Y, V.1) (Y.presheaf.stalk x) Γ(G, V.1)) :=
    Module.Flat.baseChange _ _ _
  obtain ⟨e⟩ := affine_sections_stalk_tensor_presentation G V x hx
  exact Module.Flat.of_linearEquiv e.symm

end AlgebraicGeometry
