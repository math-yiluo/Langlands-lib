/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Invertible
import all WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

/-! # Locally constructible adic sheaves as compatible local heart objects

Source: Bhatt--Scholze, Section 6.8, Definitions 6.8.6 and 6.8.8,
Propositions 6.8.4(5) and 6.8.14, and Remark 6.8.15
(blueprint: def-dl-a1-locally-constructible-adic-heart).

On a locally finite-type k0-scheme, separated finite-type opens form a basis.
A locally constructible sheaf is specified on this basis, with the canonical completed
restriction identifications and their cocycle. Different opens may use different finite
coefficient fields. Morphisms commute with every restriction identification.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (T : Over (Spec (.of D.k₀)))

section ZeroCompatibility

-- Keep the coefficient models abstract while rewriting their representative formula.
attribute [local irreducible] rationalDerivedPullback commonStagePullbackComparison
  HasDerivedCategory.standard ScalarLocalization.category
  ObjectProperty.FullSubcategory.category

end ZeroCompatibility

end WeilConjectures
