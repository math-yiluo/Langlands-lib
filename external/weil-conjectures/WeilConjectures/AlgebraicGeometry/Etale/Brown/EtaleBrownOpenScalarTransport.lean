/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenScalarTransportExistence
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownOpenScalarTransportSquare

/-! # Open scalar mate in normalized realizations

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

/-- The local open scalar square for the specified adjunction mates.
Source: Zheng, Construction 5.14 and Lemma 5.16; Stacks 07A4 and 0GL6.
(blueprint: lem-pur-etale-brown-open-scalar-transport).

Proof: first take the left-adjoint conjugate of the recorded invertible
restriction/inverse-image square under the composite scalar/open adjunctions.
Its open mate is the inverse recorded derivedTensor, by restrictedDirect_mate,
restrictedInverse_mate and the iterated-mate identity. This constructs op.
For its transport equation, transpose both paths under the published open extension/restriction
adjunction. The normalization of jo replaces its mate by the inverse normalized
inverse-image comparison. The normalization of op replaces its mate by the inverse
recorded derivedTensor. The scalar comparison is itself normalized by its scalar
restriction mate. Take a second mate along scalar restriction: the iterated-mate
identity reduces the remaining square to the identity-on-sections scalar restriction
square for inverse image. On cochain representatives this follows from the ordinary
restriction/inverse-image square and its unit formula. The derivedTensor_rep and
geometric transpose equations descend that identity through localization. Thus the
transposes are precisely the open-unit transpose defining ExceptionalCoefficients.openIso.
Injectivity of the open Hom bijection proves the square. No finite-coefficient or
boundedness assumption is needed, including the empty open and identity quotient.
This is only the open factor; no proper image or compact-support pasting enters. -/
theorem etaleBrownOpenScalarTransport
    (O : Type (u + 1)) [CommRing O] (t : O)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : StrictEtaleCompactSupport O t c)
    (RX : StrictEtaleBrownRealization O t X S.PX)
    (RZ : StrictEtaleBrownRealization O t c.Z S.PZ)
    (ro : ∀ n, StrictEtaleBrownImageRealization O t c.i n
      S.openImage (S.openDerived.level n) RX RZ)
    (jo : ∀ n, S.levelDerivedOpen n ⋙ RZ.derived n ≅
      RX.derived n ⋙ (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory)
    (hjo : ∀ n,
      (mateEquiv (S.levelDerivedOpenAdjunction n)
        (((Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
          c.i).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t n))
            c.i).rightDerivedFunctorIsoMapDerivedCategory)
        (.mk _ _ _ _ (jo n).inv)) = (ro n).inverse.inv)
    {m n : ℕ} (h : m ≤ n)
    : ∃ op : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived,
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ op.hom)) = (S.openDerived.derivedTensor h).inv ∧
    ∀ P : DerivedCategory (strictEtaleLevel X O t n),
    (RZ.derived m).map (op.inv.app P) ≫
      (jo m).hom.app ((S.PX.scalar h).derived.obj P) ≫
      (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c.i).mapDerivedCategory.map
        ((RX.scalar h).hom.app P) =
    (RZ.scalar h).hom.app ((S.levelDerivedOpen n).obj P) ≫
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) c.Z).map
        ((jo n).hom.app P) ≫
      (Etale.ExceptionalCoefficients.openIso (strictEtaleBrownRingMap O t h) c.i).hom.app
        ((RX.derived n).obj P) := by
  obtain ⟨op, hop⟩ := etaleBrownOpenScalarTransport_exists O t c S RX RZ ro jo hjo h
  refine ⟨op, hop, ?_⟩
  exact etaleBrownOpenScalarTransport_square O t c S RX RZ ro jo hjo h op hop

end AlgebraicGeometry
