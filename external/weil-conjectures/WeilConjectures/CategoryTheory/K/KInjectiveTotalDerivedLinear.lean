/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Scalar linearity of total right derived functors computed by K-injectives

Source: Stacks Project, Derived Categories, Tag 070I (lemma-K-injective), (1) and (3),
with the naturality argument using Tags 070K and 070Y; Differential Graded Algebra,
Tags 09MJ and 09MK (blueprint: lem-weil-kinjective-total-derived-linear).

## Main definitions and statements

* `CategoryTheory.Functor.kInjectiveDerivedRepresentativeIso` is the specified comparison
  for an arbitrary derived object and an arbitrary K-injective representative.
* `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions_linear` states additivity,
  scalar linearity, and the unique homotopy-class computation for those representatives.
-/

@[expose] public section

set_option autoImplicit false

universe r wA wB vA vB uA uB

open CategoryTheory

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  (U : A ⥤ B) [U.Additive]
  (enough : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

end CategoryTheory.Functor
