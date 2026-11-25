/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import all WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward

set_option linter.privateModule false

/-! # Deriving a normalized strict scalar direct-image square
Source: blueprint direct-image proof, paragraph (2).
(blueprint: lem-sp-compactification-scalar-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem normalized_inverse {C : Type*} [Category C] {A B P Q : C}
    (a : A ≅ B) (k : P ≅ Q) (t : B ⟶ P) (s : A ⟶ Q)
    (h : t ≫ k.hom = a.inv ≫ s) : s ≫ k.inv = a.hom ≫ t := by
  apply (cancel_mono k.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, ← Category.assoc, a.hom_inv_id, Category.id_comp]

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
