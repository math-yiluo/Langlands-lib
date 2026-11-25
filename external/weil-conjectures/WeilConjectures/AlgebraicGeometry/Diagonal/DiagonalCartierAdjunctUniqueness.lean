/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierCanonicalAdjunct
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerStrictTargetTransport

/-! # Cartier class uniqueness for the negative Kummer adjunct
Source: diagonal tower system proof, step (4).
(blueprint: lem-sfb-diagonal-cartier-adjunct-uniqueness). -/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] CategoryTheory.Abelian.Ext
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 11000] kummerModuleHasExt kummerAbHasExt

attribute [local irreducible] DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ diagonalDerivedSingleCounit
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison cartierRootsIso
  cartierEtaleKummerUnit cartierProKummerUnit cartierProIntegralGenerator cartierProRootMap
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

/-- Cancel the two signs and reassociate before specializing the category. -/
private theorem double_negative_ext_associativity
    {A : Type*} [Category A] [Abelian A] [HasExt.{w} A]
    {S X M U P : A} (α : Ext S X 0) (β : Ext X M 1)
    (γ : Ext M U 0) (κ : Ext U P 1) :
    negativeExtProduct (-(α.comp β (zero_add 1))) (γ.comp κ (zero_add 1)) =
      (α.comp (β.comp γ (add_zero 1)) (zero_add 1)).comp κ rfl := by
  unfold negativeExtProduct
  rw [Ext.neg_comp, neg_neg]
  simp only [Ext.comp_assoc]

/-- The finite diagonal Cartier classes with the named coefficient structures.
This is the existing uniquely determined Cartier class, specialized to the
surface and collected into a family so its concrete interfaces are shared.
Source: diagonal tower system proof, step (4)
(blueprint: lem-sfb-diagonal-cartier-adjunct-uniqueness). -/
def diagonalResidueClasses (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤))) :
    ∀ n : ℕ, Ext.{u + 1}
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)) 2 :=
  fun n =>
    letI : Finite (diagonalResidue.{u} ℓ n) :=
      cartierResidue_finite ℓ (Fact.out : ℓ.Prime) (n + 1)
    canonicalCartierClass (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (cartierResidue_cast ℓ (n + 1))
      (diagonalImmersion Y) (diagonalImmersion_cartier Y)
      (diagonalSurface_power_unit ℓ Y hY n)

/-- The negative Kummer adjunct of the positive diagonal boundary is the
normalized residue Cartier class.

Source: diagonal tower system proof, step (4), and the defining scalar-adjunct
characterization of the Cartier reduction
(blueprint: lem-sfb-diagonal-cartier-adjunct-uniqueness).

Proof: expand the positive integral boundary as minus the transported pole
boundary. The negative sign of Kummer transport cancels this sign by bilinearity
of the Ext product. Associativity moves the units comparison into the transported
pole boundary, giving exactly CartierProReductionSpec. The residue ring is
finite, since the prime power is positive. The pro-etale component of
cartierReduction_existsUnique then identifies e with the chosen unique class,
which is the definition of cartierResidueReducedPro. Only the equality of the
full scalar adjunct is used. In particular this proof does not infer equality
from a Chern composite and does not involve a derived reduction presentation,
source normalization, target system or evaluation. The proof hW is any proof
that the prime is a unit on the surface; its powers and the pulled-back powers
from hY agree by proof irrelevance. -/
theorem diagonal_cartier_class_of_adjunct (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (hW : IsUnit (ℓ : Γ(diagonalSurface Y, ⊤))) (n : ℕ)
    (e : Ext.{u + 1}
      ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
        (diagonalImmersion Y)).obj
          (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y)))
      (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
        (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)) 2)
    (he : kummerScalarAdjunct (A := DiagonalAb (diagonalSurface Y))
      (cartierForget (diagonalResidue.{u} ℓ n) (diagonalSurface Y))
      (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n) (diagonalImmersion Y)) e =
      negativeExtProduct (diagonalIntegralBoundary Y)
        (kummerComparedUnit ℓ (diagonalSurface Y) hW n)) :
    e = diagonalResidueClasses ℓ Y hY n := by
  have hspec : (Ext.mk₀ (cartierProIntegralGenerator (diagonalResidue.{u} ℓ n)
        (diagonalImmersion Y))).comp
      (e.mapExactFunctor (cartierForget (diagonalResidue.{u} ℓ n) (diagonalSurface Y)))
      (zero_add 2) =
      (cartierProBoundary (diagonalImmersion Y)
        (Etale.cartierPoleBoundary (diagonalImmersion Y) (diagonalImmersion_cartier Y))).comp
        (cartierProKummerUnit (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) rfl := by
    unfold kummerScalarAdjunct kummerComparedUnit at he
    refine he.trans ?_
    unfold diagonalIntegralBoundary transportBoundarySource
      cartierProBoundary cartierBoundaryImage
    exact double_negative_ext_associativity _ _ _ _
  let : Finite (diagonalResidue.{u} ℓ n) :=
    cartierResidue_finite ℓ (Fact.out : ℓ.Prime) (n + 1)
  unfold diagonalResidueClasses
  exact canonical_cartier_class_of_adjunct (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (cartierResidue_cast ℓ (n + 1))
    (diagonalImmersion Y) (diagonalImmersion_cartier Y)
    (diagonalSurface_power_unit ℓ Y hY n) e hspec

end AlgebraicGeometry.ProEtale
