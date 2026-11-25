/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Restriction of scalars is lax braided

For a morphism `f : R →+* S` of commutative rings, the lax monoidal restriction of scalars
`ModuleCat S ⥤ ModuleCat R` is compatible with the symmetric braidings: both
`M ⊗_R N ⟶ N ⊗_S M` send `m ⊗ n` to `n ⊗ m`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal TensorProduct

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of scalars along a morphism of commutative rings is lax braided. -/
noncomputable instance laxBraided_restrictScalars : (restrictScalars.{u} f).LaxBraided where
  braided M N := by
    refine MonoidalCategory.tensor_ext (fun m n ↦ ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    erw [restrictScalars_μ_tmul]

end ModuleCat
