/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportOriginRestrictionComposition

/-! # Finite coefficient comparison and compact-support composition

Source: Stacks Project, more-etale.tex, Tags 0F7J and 0GL6
(blueprint: lem-sf-compact-coefficient-composition).
The two statements use the actual small-etale and pro-etale compact-support functors,
the specified canonical compositors, and universal B-linear coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIntegers
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] originCompositionAmbient

/-- Positive-level coefficient rings in the standard coefficient universe are finite.
This only registers the recorded coefficient finiteness theorem at positive levels.
Source: Serre, Local Fields, Chapter II, section 2; Stacks Tag 0GL6
(blueprint: lem-sf-compact-coefficient-composition). -/
instance finiteCompositionCoefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ+) : Finite (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)

/-- The specified quotient coefficient homomorphism, with only the standard universe lift.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-coefficient-composition). -/
def finiteCompositionReduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (m n : ℕ+) (hmn : n ≤ m) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E m) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E n) :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E m)
    (T := Padic.coefficientExtensionIdeal l E n) (Ideal.pow_le_pow_right hmn))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Etale

private theorem restriction_map_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (T : Scheme.{u})
    {M N : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (z : M ⟶ N) :
    ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map z).hom =
      (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ).map z.hom := by
  rfl

private theorem tensor_map_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (z : K ⟶ L) :
    M.unit ≫ (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      (M.map N z) = z ≫ N.unit := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, restriction_map_hom]
  exact (Equiv.ofBijective _ (M.universal _)).apply_symm_apply _

private theorem comparison_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.unit ≫ (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus.map
      (compactSupportCoefficientComparisonPlus c M N) =
    (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, restriction_map_hom]
  exact (Equiv.ofBijective _ (N.universal _)).apply_symm_apply _

attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus
attribute [local irreducible] Functor.mapDerivedCategory
  Functor.rightDerivedFunctor
attribute [local implicit_reducible] derivedPlusFormalism
attribute [local irreducible] compactSupportCoefficientRestrictionPlus
attribute [local implicit_reducible] ExchangeFormalism.shriek
attribute [local irreducible] rightDerivedLowerShriekPlusCompIso
  compactSupportCoefficientComparisonPlus CoefficientTensorModel.map

end AlgebraicGeometry.Etale
