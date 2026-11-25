/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerSystem
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization

/-!
# Ordinary Chern realization of a normalized supported Kummer class

Source: Stacks 03PL and 0A45; blueprint lem-asd-ordinary-supported-kummer.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000] ordinaryFiniteClass._proof_1 ordinaryFiniteClass._proof_2
  ordinaryFiniteClass._proof_3

/-- Forgetting support in the uniquely normalized class gives the ordinary divisor Chern class.
Source: Stacks 03PL and 0A45; the unit and scalar-Chern clauses of
`ordinary_supported_kummer` (auxiliary; not a blueprint node).

Proof: unfold the ordinary finite-class realization. The proved unit-forgetting
equation identifies this class with the supported integral unit and generator
composite. The proved supported Chern realization identifies exactly that composite
with the divisor Chern class. Compose these two equalities. Positivity and finiteness
are retained in the public signature but are not needed for this identity. -/
theorem ordinary_supported_kummer_chern (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2
      (supportedDerivedUnit A i ≫ supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} A) i) (ordinaryFiniteConstant A D)
        (Scheme.finiteEtaleTateLine T N A hA) κ) =
      supportedKummerChern A N hA i hI hT := by
  have _hN : 0 < N := hN
  unfold ordinaryFiniteClass
  exact (supported_derived_unit_forget A i (Scheme.finiteEtaleTateLine T N A hA) κ).trans
    (supported_kummer_chern_realization T N A hA hT i hI κ hκ)

end AlgebraicGeometry.Etale
