/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TensorBicomplex


public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Tensoring a chain map with a module map

The unsigned tensor bicomplex and its maps are compatibility abbreviations for
Mathlib `Functor.mapBifunctorHomologicalComplex` and the map of its uncurried
bifunctor (`Functor.uncurry.obj`).
The names remain available to downstream modules; no separate construction is used.
In particular, `tensorBicomplexMap` is the map supplied by the uncurried
bifunctor, so its chain-map identities are inherited from Mathlib.
The compatibility names therefore unfold directly to the library's canonical map.

Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

/-- The commuting tensor bicomplex, with terms `Pᵢ ⊗ Qⱼ` and no totalization signs.
This compatibility abbreviation is the canonical Mathlib bifunctor object.
Its terms and commuting differentials are inherited definitionally.
Source: Stacks Project, Algebra, Tag 00M3, proof, first paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P).obj Q

/-- Compatibility abbreviation for the canonical Mathlib bifunctor map.
A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  dsimp% only [Functor.uncurry] (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)



end HomologicalComplex₂
