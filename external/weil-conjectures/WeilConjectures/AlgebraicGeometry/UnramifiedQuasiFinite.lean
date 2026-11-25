/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Unramified morphisms are locally quasi-finite

Source: Stacks Project, Morphisms, Lemma 02V5 and Algebra, Lemma 02UR
(blueprint: lem-weil-pbc-unramified-quasi-finite-at-points).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

/-- An unramified morphism is quasi-finite at every point.

Source: Stacks Project, Morphisms, Lemma 02V5 and Algebra, Lemma 02UR
(blueprint: lem-weil-pbc-unramified-quasi-finite-at-points).
The proof chooses affine neighbourhoods, obtains finite type and formal unramifiedness
for the induced section-ring map, and applies Mathlib's finite-type formally-unramified
algebra instance to make the fibre spectrum discrete.
-/
theorem isLocallyQuasiFinite_of_unramified
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) :
    IsLocallyQuasiFinite f := by
  let : LocallyOfFiniteType f := hf.1
  let : IsOpenImmersion (pullback.diagonal f) := hf.2
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  refine ⟨U, hxU, hU, V, hV, hUV, ?_⟩
  let := (f.appLE V U hUV).hom.toAlgebra
  have hft : Algebra.FiniteType Γ(Y, V) Γ(X, U) := f.finiteType_appLE hV hU hUV
  let := hft
  have hfu : Algebra.FormallyUnramified Γ(Y, V) Γ(X, U) :=
    f.formallyUnramified_appLE hV hU hUV
  let := hfu
  refine ⟨hft, ?_⟩
  unfold Algebra.IsQuasiFiniteAtPrime
  exact isOpen_discrete _

end AlgebraicGeometry.Scheme.Hom
