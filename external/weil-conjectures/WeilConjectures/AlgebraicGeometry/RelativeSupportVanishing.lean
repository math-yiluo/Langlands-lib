/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.KrullDimension.Basic

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-! # Lower vanishing for the supported complex of a smooth pair

Source: Stacks Project, Tags 0FUE and 09XP; the normal-coordinate argument in
lem-pur-relative-support-bottom-descent, Steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

-- STATEMENT-DISPUTED: the former codimension convention allowed infinite ambient
-- stalk dimensions. The returned E2 repair adds hfinite before using that convention.
/-- The derived sheaf of closed-supported sections of a signed finite Tate coefficient
vanishes below twice the codimension of a smooth pair with finite-dimensional ambient
stalks. The finite-dimensional stalk hypothesis explicitly rules out using the
codimension equation at infinity, where addition cannot determine the codimension.
No frame or orientation is needed for this vanishing assertion.
Source: Stacks Project, Tags 0FUE and 09XP; blueprint main-20261015,
sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md, local coordinate argument
(blueprint: lem-pur-relative-support-vanishing).

Proof: At a geometric point on the support choose simultaneous etale coordinates for
(V,Z) over B, and pull the chart back along e. Etale restriction is exact and preserves
injectives; its ordinary kernel identification therefore identifies the supported
derived stalks. The relative support coordinate model identifies the stalk with the
global supported complex of the origin in affine b-space over the fixed algebraically
closed field k. The codimension clause of that model gives b=c on every chart meeting
the support, using the dimension equation at all points of Z, without cancelling an
infinite Krull dimension. The finite-type coordinate support orientation over Spec k
concentrates this field complex in degree 2b. Changing the annihilating exponent from
the coefficient-ring characteristic to the universal ell-power preserves the signed
finite Tate sheaf by the exponent comparison; all exponents in question are positive
and invertible over k. Thus every supported stalk vanishes below 2c. The finite-dimensional
ambient-stalk hypothesis is used when passing from the displayed Krull-dimension equality
to the finite relative codimension in the local coordinate model. Outside the support the
complementary open adjunction unit is invertible locally, so its kernel and derived stalk
vanish. Forgetting scalars is exact and commutes with the restriction kernels. The underlying
injective module sheaves are acyclic for
restriction and for the supported kernel (check on etale objects using the support
exact sequence), so the module calculation computes the same derived abelian support
sheaf. Exact geometric stalks commute with cohomology, and their conservativity gives
the asserted zero sheaf. This also covers c=0 (only negative degrees) and empty support.
-/
theorem relative_support_vanishing
    (P : WeilConjectures.PurityFiniteSetting.{u}) (c d : ℕ)
    {B V Z U : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension d v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)]
    (hcodim : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) =
        ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞))
    (hfinite : ∀ z : Z,
      ringKrullDim (V.presheaf.stalk (i.base z)) ≠ ⊤)
    (e : U ⟶ V) [Etale e] (r : ℤ) :
    ∀ q : ℤ, q < 2 * (c : ℤ) →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
          ((sectionsWithSupport AddCommGrpCat.{u + 1}
            (pullback.snd i e).openComplement.ι).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((P.forgetEtale U).obj
                (Scheme.finiteEtaleTateSheaf P.Coefficient (ringChar P.Coefficient) U
                  (CharP.cast_eq_zero P.Coefficient (ringChar P.Coefficient)) r))))) := by
  sorry

end AlgebraicGeometry.Etale
