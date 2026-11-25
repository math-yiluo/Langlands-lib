/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.RingHomExtensionDefs

set_option linter.privateModule false

/-! # Transport of a module Hom comparison to the one-point ring site

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom and
Lemma 0A6A; the one-point-site realization used in the parent statement.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace CategoryTheory

private theorem point_eq (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
    U = op ⟨PUnit.unit⟩ := by
  rcases U with ⟨⟨⟨⟩⟩⟩
  rfl

end CategoryTheory
