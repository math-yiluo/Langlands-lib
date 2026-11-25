/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction

/-!
# The relative interpretation of the exceptional adjoint

The statement below spells out exactly the class-restricted vanishing and natural
relative Hom bijections. It imposes no ambient exceptional datum.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

section FixedCounit

open scoped CategoryTheory.Functor

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  [CompactSpace Y] [QuasiCompact f]

variable [HasCompactification f]

private noncomputable def fixedAdjunction :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c ⊣
      Etale.rightDerivedUpperShriek Λ f :=
  (Etale.rightDerivedUpperShriekAdjunction Λ f).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso Λ c).symm

end FixedCounit

end AlgebraicGeometry.ProEtale
