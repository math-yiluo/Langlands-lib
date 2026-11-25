/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields

/-! # Locally closed generators for constructible condensed modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Single sheaves obtained by extension by zero from an open in a closed subscheme,
with a locally finitely presented coefficient module on the open.
Source: the open/closed steps of Hemo--Richarz--Scholbach, Lemma 5.3(2).
(auxiliary; not a blueprint node) -/
def condensedConstructiblePiece
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj E.val) T))) :=
  condensedLocallyClosedPiece (Profinite.continuousMapRingObj E.val) T

end AlgebraicGeometry.ProEtale
