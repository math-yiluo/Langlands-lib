/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Homology of locally constant module-valued cochains

Source: blueprint `proposition-local-structure-integral-constructible-complexes`, Compatible
isomorphisms, identification of constant quotient cohomology and its sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v r
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Locally constant module-valued functions, with scalar maps acting by postcomposition.
Source: Stacks Tag 093J; blueprint Compatible isomorphisms.
(blueprint: lem-pe-locally-constant-module-homology). -/
def locallyConstantModuleFunctor (T : Type v) [TopologicalSpace T]
    (R : Type r) [Ring R] : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (LocallyConstant T M)
  map f := ModuleCat.ofHom (LocallyConstant.mapₗ R f.hom)
  map_id M := by ext f x; rfl
  map_comp f g := by ext s x; rfl

instance locallyConstantModuleFunctor_additive (T : Type v) [TopologicalSpace T]
    (R : Type r) [Ring R] : (locallyConstantModuleFunctor T R).Additive where
  map_add := by intros; rfl

end AlgebraicGeometry.ProEtale
