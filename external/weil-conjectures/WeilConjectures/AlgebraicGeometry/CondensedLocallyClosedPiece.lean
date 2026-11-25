/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Locally closed generators for constructible condensed modules -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Locally closed single-sheaf generators for a fixed commutative condensed ring.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), open/closed steps.
(auxiliary; not a blueprint node)

This is the coefficient-abstract form of the existing finite-field generator predicate.
Keeping the coefficient abstract avoids repeated expansion of the sheafification and
monoidal structures when the predicate is eliminated. Its data are exactly a closed
immersion, a quasi-compact open immersion, a locally finitely presented module, and an
isomorphism with its extension by zero concentrated in degree zero. -/
def condensedLocallyClosedPiece
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj Λ T))) :=
  fun K ↦ ∃ (Z U : Scheme.{u}) (i : Z ⟶ T) (j : U ⟶ Z),
    Exists fun [_hi : IsClosedImmersion i] ↦ Exists fun [_hj : IsOpenImmersion j] ↦
      QuasiCompact j ∧ ∃ (P : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
        (condensedRingObj Λ U)),
        IsLocallyFinitelyPresented
          (condensedRingObj Λ U) P ∧
        Nonempty (K ≅ (DerivedCategory.singleFunctor _ 0).obj
          ((CondensedRing.lowerStar Λ i).obj
            ((CondensedRing.openImmersionLowerShriek Λ j).obj P)))

end AlgebraicGeometry.ProEtale
