/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData

/-! # Normalized realization for Brown coefficient projection

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CV, 06YY and 07A4
(blueprint: def-pur-etale-brown-projection-realization).

These are comparison interfaces only. They impose no condition on the coefficient
parameter and make no existence assertion. All ordinary functors are the recorded
ones, and the equations fix localization and adjunction comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
variable (O : Type (u + 1)) [CommRing O] (t : O)

/-- The already used quotient ring, with positive exponent `n+1`.
Source: Zheng, Construction 4.1
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev strictEtaleBrownRing (n : ℕ) := O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)

/-- The actual quotient homomorphism, including the identity case.
Source: Zheng, Construction 4.1
(blueprint: def-pur-etale-brown-projection-realization). -/
def strictEtaleBrownRingMap {m n : ℕ} (h : m ≤ n) :
    strictEtaleBrownRing O t n →+* strictEtaleBrownRing O t m :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Reuse the coefficient-projection node's restriction to constant scalars.
Source: Zheng, Construction 4.1; Stacks 03CV
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev strictEtaleBrownConstant (W : Scheme.{u}) (n : ℕ) :=
  Etale.SystemProjection.constantModule W (.of (strictEtaleBrownRing O t n))

/-- Conclusion data realizing the fixed-ring encoding, with all comparisons normalized.
The ordinary functor is the recorded constant-scalar restriction, not a new realization.
Scalar comparison is its adjoint mate after exact localization.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV, 06YY
(blueprint: def-pur-etale-brown-projection-realization). -/
structure StrictEtaleBrownRealizationData (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) where
  [ordinaryAdditive : ∀ n, (strictEtaleBrownConstant O t W n).Additive]
  derived : ∀ n, DerivedCategory (strictEtaleLevel W O t n) ⥤
    Etale.DerivedCategoryModule (strictEtaleBrownRing O t n) W
  factors : ∀ n, DerivedCategory.Q ⋙ derived n ≅
    (strictEtaleBrownConstant O t W n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  [equivalence : ∀ n, (derived n).IsEquivalence]
  ordinaryRestriction : ∀ {m n : ℕ} (h : m ≤ n),
    coefficientRestriction (J := W.smallEtaleTopology) O t h ⋙
      strictEtaleBrownConstant O t W n ≅
    strictEtaleBrownConstant O t W m ⋙
      Sheaf.restrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)
  restriction : ∀ {m n : ℕ} (h : m ≤ n),
    (P.scalar h).restriction ⋙ derived n ≅ derived m ⋙
      Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)
  scalar : ∀ {m n : ℕ} (h : m ≤ n),
    (P.scalar h).derived ⋙ derived m ≅
      derived n ⋙ Etale.scalarExtension (strictEtaleBrownRingMap O t h) W

/-- Section, localization and adjunction equations specifying the realization maps.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CV, 06YY
(blueprint: def-pur-etale-brown-projection-realization). -/
def StrictEtaleBrownRealizationCoherence (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealizationData O t W P) : Prop :=
  letI := R.ordinaryAdditive
  (∀ {m n : ℕ} (h : m ≤ n)
    (M : strictEtaleLevel W O t m) (U : W.Etaleᵒᵖ) (x : M.val.obj U),
    HEq (((R.ordinaryRestriction h).hom.app M).hom.app U x) x) ∧
  (∀ {m n : ℕ} (h : m ≤ n)
    (K : CochainComplex (strictEtaleLevel W O t m) ℤ),
    (R.restriction h).hom.app (DerivedCategory.Q.obj K) ≫
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).map ((R.factors m).hom.app K) ≫
      (Sheaf.restrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)).mapDerivedCategoryFactors.hom.app
          (((strictEtaleBrownConstant O t W m).mapHomologicalComplex (.up ℤ)).obj K) =
    (R.derived n).map ((P.scalar h).restrictionFactors.hom.app K) ≫
      (R.factors n).hom.app
        (((coefficientRestriction (J := W.smallEtaleTopology) O t h).mapHomologicalComplex
          (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (R.ordinaryRestriction h) (.up ℤ)).hom.app K)) ∧
  (∀ {m n : ℕ} (h : m ≤ n),
    (mateEquiv (P.scalar h).derivedAdj
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology
        (strictEtaleBrownRingMap O t h)))
      (.mk _ _ _ _ (R.scalar h).inv)) = (R.restriction h).hom)

/-- The fixed realization with its canonical comparison equations.
Source: Zheng, Construction 4.1 and Lemma 5.16
(blueprint: def-pur-etale-brown-projection-realization). -/
def StrictEtaleBrownRealization (W : Scheme.{u}) (P : StrictEtaleEvaluation W O t) :=
  { R : StrictEtaleBrownRealizationData O t W P //
    StrictEtaleBrownRealizationCoherence O t W P R }

section
variable {O t} {W : Scheme.{u}} {P : StrictEtaleEvaluation W O t}

/-- The specified derived realization. Source: Zheng 4.1
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev StrictEtaleBrownRealization.derived (R : StrictEtaleBrownRealization O t W P) :=
  R.val.derived

/-- The specified localization comparison. Source: Zheng 4.1
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev StrictEtaleBrownRealization.factors (R : StrictEtaleBrownRealization O t W P) :=
  R.val.factors

/-- The specified scalar mate. Source: Zheng 4.1 and 5.16
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev StrictEtaleBrownRealization.scalar (R : StrictEtaleBrownRealization O t W P)
    {m n : ℕ} (h : m ≤ n) := R.val.scalar h

end

/-- The published right-derived unit on a cochain representative.
Source: Stacks 07A4
(blueprint: def-pur-etale-brown-projection-realization). -/
def strictEtaleBrownRightUnit {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (K : CochainComplex
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))) ℤ) :
    DerivedCategory.Q.obj
      (((Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
      g).rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app K)

/-- Conclusion data comparing geometric images in the two coefficient encodings.
The section equation fixes ordinary direct image. Its universal derived-unit square
fixes derived direct image, and the mate equation fixes inverse image.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4
(blueprint: def-pur-etale-brown-projection-realization). -/
structure StrictEtaleBrownImageRealizationData
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW) where
  ordinaryRight : A.right n ⋙ strictEtaleBrownConstant O t W n ≅
    strictEtaleBrownConstant O t V n ⋙
      Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g
  right : B.direct ⋙ RW.derived n ≅ RV.derived n ⋙
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).rightDerivedFunctor
  inverse : RW.derived n ⋙
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).mapDerivedCategory ≅
    B.inverse ⋙ RV.derived n

/-- All comparisons are fixed on sections, representatives and Hom adjunctions.
Source: Zheng, Construction 5.15 and Lemma 5.16; Stacks 07A4
(blueprint: def-pur-etale-brown-projection-realization). -/
def StrictEtaleBrownImageRealizationCoherence
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (R : StrictEtaleBrownImageRealizationData O t g n A B RV RW) : Prop :=
  letI := RV.val.ordinaryAdditive
  letI := RW.val.ordinaryAdditive
  (∀ (M : strictEtaleLevel V O t n) (U : W.Etaleᵒᵖ)
    (x : ((A.right n).obj M).val.obj U),
    (R.ordinaryRight.hom.app M).hom.app U x =
      ((A.rightUnderlying n).hom.app M).hom.app U x) ∧
  (∀ K : CochainComplex (strictEtaleLevel V O t n) ℤ,
    (RW.derived n).map (B.directUnit.app K) ≫ R.right.hom.app (DerivedCategory.Q.obj K) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
        g).rightDerivedFunctor.map ((RV.factors n).hom.app K) =
    (RW.factors n).hom.app (((A.right n).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex R.ordinaryRight.hom (.up ℤ)).app K) ≫
      strictEtaleBrownRightUnit O t g n
        (((strictEtaleBrownConstant O t V n).mapHomologicalComplex (.up ℤ)).obj K)) ∧
  ((mateEquiv B.adjunction
    (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).mapDerivedCategoryRightDerivedAdjunction
    (.mk _ _ _ _ R.inverse.hom)) = R.right.hom)

/-- The normalized geometric comparison interface, without an existence assertion.
Source: Zheng, Construction 5.15 and Lemma 5.16
(blueprint: def-pur-etale-brown-projection-realization). -/
def StrictEtaleBrownImageRealization
    {V W : Scheme.{u}} (g : V ⟶ W) (n : ℕ)
    (A : StrictEtaleOrdinaryImage O t g)
    (B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n))
    {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW) :=
  { R : StrictEtaleBrownImageRealizationData O t g n A B RV RW //
    StrictEtaleBrownImageRealizationCoherence O t g n A B RV RW R }

section
variable {O t} {V W : Scheme.{u}} {g : V ⟶ W} {n : ℕ}
  {A : StrictEtaleOrdinaryImage O t g}
  {B : CoefficientDerivedImage (A.lift n).modules (A.right n) (A.levelAdj n)}
  {PV : StrictEtaleEvaluation V O t} {PW : StrictEtaleEvaluation W O t}
  {RV : StrictEtaleBrownRealization O t V PV}
  {RW : StrictEtaleBrownRealization O t W PW}

/-- The normalized derived proper comparison. Source: Zheng 5.15 and 5.16
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev StrictEtaleBrownImageRealization.right
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW) := R.val.right

/-- The adjunction-normalized inverse comparison. Source: Zheng 5.15 and 5.16
(blueprint: def-pur-etale-brown-projection-realization). -/
abbrev StrictEtaleBrownImageRealization.inverse
    (R : StrictEtaleBrownImageRealization O t g n A B RV RW) := R.val.inverse

end
end AlgebraicGeometry
