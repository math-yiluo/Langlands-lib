/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDualPairing
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Pullback of duals of finite locally free modules

Source: the finite free calculation in Stacks Project, Modules, Example 0FNV,
and pullback of locally free modules, Lemma 01C8.
(blueprint: lem-ag-pullback-dual-finite-locally-free)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback commutes with duals of finite locally free modules.

Source: Stacks Project, Modules, Example 0FNV and Lemma 01C8.

Proof: the evaluation pairing `M ⊗ dual M ⟶ O_X` pulls back to a pairing
`e^*M ⊗ e^*(dual M) ⟶ O_S`, using the tensor and unit comparisons of pullback.
Its transpose is a canonical map `e^*(dual M) ⟶ dual (e^*M)`. For each point of
`S`, choose a neighbourhood of its image on which `M` is finite free of rank `r`.
On the inverse image of this neighbourhood the map is the comparison
`O_S^r ⟶ Hom(O_S^r, O_S)`, which sends each dual basis vector to its coordinate
functional and is an isomorphism, including when `r = 0`. Thus the canonical map
is locally an isomorphism on an open cover, hence an isomorphism of sheaves.
Take its associated isomorphism.

(blueprint: lem-ag-pullback-dual-finite-locally-free) -/
theorem nonempty_pullback_dual_iso_of_isFiniteLocallyFree
    {X S : Scheme.{u}} (e : S ⟶ X) (M : X.Modules) [M.IsFiniteLocallyFree] :
    Nonempty ((pullback e).obj (dual M) ≅ dual ((pullback e).obj M)) := by
  obtain ⟨p⟩ := nonempty_exactPairing_dual_of_isFiniteLocallyFree M
  let : ExactPairing (dual M) M := p
  let : ExactPairing ((pullback e).obj (dual M)) ((pullback e).obj M) :=
    ExactPairing.map (pullback e) (dual M) M
  exact ⟨(MonoidalClosed.ihomObjUnitIso
    ((pullback e).obj (dual M)) ((pullback e).obj M)).symm⟩

end AlgebraicGeometry.Scheme.Modules
