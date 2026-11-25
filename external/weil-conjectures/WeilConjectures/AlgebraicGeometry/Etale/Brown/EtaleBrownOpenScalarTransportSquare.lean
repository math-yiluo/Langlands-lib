/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownInverseRealizationRepresentatives
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownScalarInverseRealizationCube
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.OpenScalarExchangeMate
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! # Open scalar transport decomposition

Source: Zheng, Construction 4.1, Constructions 5.14--5.15 and Lemma 5.16;
Stacks 03CY, 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
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

private theorem iso_transport_square
    {T : Type*} [Category T] {A B C D E F : T}
    (a : A ≅ B) (b : B ≅ C) (c : C ≅ D)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ D)
    (h : c.hom ≫ f.inv ≫ e.inv = b.inv ≫ a.inv ≫ d.hom) :
    a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom := by
  apply (cancel_mono (f.inv ≫ e.inv)).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun z ↦ a.hom ≫ b.hom ≫ z) h

/-- The normalized open scalar mate satisfies the transport square.
Source: Zheng, Constructions 5.14--5.15 and Lemma 5.16; Stacks 03S6, 07A4.
(blueprint: lem-pur-etale-brown-open-scalar-transport-square).

The proof transposes both paths through the open adjunction, applies the
normalization of the supplied comparison `jo` and of the supplied mate `op`,
and uses the scalar/open exchange identity on cochain representatives. -/
theorem etaleBrownOpenScalarTransport_square
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
    {m n : ℕ} (h : m ≤ n) (op : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived)
    (hop :
      (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
        (.mk _ _ _ _ op.hom)) = (S.openDerived.derivedTensor h).inv) :
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
        ((RX.derived n).obj P)  := by
  classical
  let b (k : ℕ) :=
    ((Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) c.i
      ).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoRight
      (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
        c.i).rightDerivedFunctorIsoMapDerivedCategory
  obtain ⟨e, he⟩ := Classical.axiomOfChoice (fun k ↦
    etaleBrownInverseRealization_representatives O t c.i k S.openImage
      (S.openDerived.level k) RX RZ (ro k))
  have hc := etaleBrownScalarInverseRealization_cube O t c.i S.openImage S.PZ S.PX
    S.openDerived RX RZ ro e he h
  have hi (k : ℕ) (M : DerivedCategory (strictEtaleLevel X O t k)) :=
    unit_mateEquiv (S.levelDerivedOpenAdjunction k) (b k)
      (.mk _ _ _ _ (jo k).inv) M
  have hd (M : DerivedCategory (strictEtaleLevel X O t n)) :=
    unit_mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ op.hom) M
  have hde (M : Etale.DerivedCategoryModule (strictEtaleBrownRing O t n) X) :
      (b m).unit.app ((Etale.scalarExtension (strictEtaleBrownRingMap O t h) X).obj M) ≫
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
          c.i).mapDerivedCategory.map
          ((Etale.ExceptionalCoefficients.openIso (strictEtaleBrownRingMap O t h)
            c.i).inv.app M) =
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) X).map ((b n).unit.app M) ≫
        (Etale.properOpenCoefficientPullbackIso (strictEtaleBrownRingMap O t h)
          c.i).inv.app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) c.i).mapDerivedCategory.obj M) := by
    have hb (k : ℕ) : b k = Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) c.i := by
      exact (Etale.exact_right_adj
        (Etale.openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (strictEtaleBrownRing O t k)) c.i)).symm
    simp only [hb]
    rw [Etale.compactScalarOpen_normalization]
    change ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c.i).homEquiv _ _)
        (Etale.properOpenCoefficientOpenInverse (strictEtaleBrownRingMap O t h) c.i M) = _
    unfold Etale.properOpenCoefficientOpenInverse
    exact Equiv.apply_symm_apply _ _
  intro P
  have hh := Adjunction.openScalar_exchange_of_unit
    (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m) (b n) (b m)
    (S.PX.scalar h).derived (Etale.scalarExtension (strictEtaleBrownRingMap O t h) X)
    (S.PZ.scalar h).derived (Etale.scalarExtension (strictEtaleBrownRingMap O t h) c.Z)
    (RX.derived n) (RX.derived m) (RZ.derived n) (RZ.derived m)
    (RZ.scalar h).symm (RX.scalar h).symm (ro n).inverse (ro m).inverse
    (S.openDerived.derivedTensor h).symm
    (Etale.properOpenCoefficientPullbackIso (strictEtaleBrownRingMap O t h) c.i).symm
    (jo n).inv (jo m).inv op.hom
    (Etale.ExceptionalCoefficients.openIso (strictEtaleBrownRingMap O t h) c.i).inv
    (fun M ↦ by
      rw [← hjo n]
      exact (hi n M).symm)
    (fun M ↦ by
      rw [← hjo m]
      exact (hi m M).symm)
    (fun M ↦ by
      change _ = _ ≫ (S.openDerived.derivedTensor h).inv.app _
      rw [← hop]
      exact (hd M).symm)
    hde hc P
  exact iso_transport_square
    ((RZ.derived m).mapIso (op.symm.app P))
    ((jo m).app ((S.PX.scalar h).derived.obj P))
    ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) c.i).mapDerivedCategory.mapIso
        ((RX.scalar h).app P))
    ((RZ.scalar h).app ((S.levelDerivedOpen n).obj P))
    ((Etale.scalarExtension (strictEtaleBrownRingMap O t h) c.Z).mapIso ((jo n).app P))
    ((Etale.ExceptionalCoefficients.openIso (strictEtaleBrownRingMap O t h) c.i).app
      ((RX.derived n).obj P)) hh

end AlgebraicGeometry
