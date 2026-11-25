/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubobjectKernel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalQuotientVanishing

/-! # Effectivity of the kernel construction for compatible local subobjects

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The canonical comparison from the explicitly constructed kernel is an
isomorphism when the local subobjects agree on overlaps.

Source: Stacks Project, Sites, Tag 04TR.
(auxiliary; not a blueprint node).

Proof: the overlap calculation shows that q_i has zero composite with the
restriction of the simultaneous quotient map. Inverse image along U_i preserves
the kernel, so q_i factors through the restricted constructed subobject. The
canonical comparison and this factor are inverse, by cancellation of the
monomorphisms q_i and the restricted kernel inclusion. -/
theorem isIso_localSubobjectKernelComparison
    (X : Scheme.{u}) (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
    (q : ∀ i, L i ⟶ (upperStar Ab.{u + 1} (U.f i)).obj Q)
    (hq : ∀ i, Mono (q i))
    (hcompatible : ∀ i j, ∃ c :
      (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i) ≅
        (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j),
      c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j) =
        (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i) ≫
          (upperStarCompIso Ab.{u + 1}
            (pullback.condition (f := U.f i) (g := U.f j))).hom.app Q) :
    ∀ i, IsIso (localSubobjectKernelComparison X Q U L q hq i) := by
  intro i
  exact isIso_localSubobjectKernelComparison_of_zero X Q U L q hq i
    (localSubobjectQuotientMap_zero_of_compatible X Q U L q hcompatible i)

end AlgebraicGeometry.ProEtale
