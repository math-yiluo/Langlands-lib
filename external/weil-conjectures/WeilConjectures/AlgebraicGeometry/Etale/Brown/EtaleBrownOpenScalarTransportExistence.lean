/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Open scalar transport decomposition

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
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

section MateCalculus
universe a av b bv c cv d dv
variable {A : Type a} [Category.{av} A] {B₀ : Type b} [Category.{bv} B₀]
  {C : Type c} [Category.{cv} C] {D : Type d} [Category.{dv} D]

-- Hom transposition identifies the recorded scalar comparison and its double mate.
private theorem conjugate_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (P : A) (Q : B₀) (f : L.obj P ⟶ Q) :
    b.homEquiv P Q (e.hom.app P ≫ f) =
      a.homEquiv P Q f ≫ (conjugateIsoEquiv a b e).hom.app Q := by
  rw [a.homEquiv_unit, b.homEquiv_unit, Category.assoc]
  rw [show R.map f ≫ (conjugateIsoEquiv a b e).hom.app Q =
    (conjugateIsoEquiv a b e).hom.app (L.obj P) ≫ R'.map f from
      (conjugateIsoEquiv a b e).hom.naturality f]
  rw [← Category.assoc]
  erw [unit_conjugateEquiv]
  simp only [Functor.map_comp, Category.assoc]

private theorem conjugate_of_transpose
    {L L' : A ⥤ B₀} {R R' : B₀ ⥤ A} (a : L ⊣ R) (b : L' ⊣ R')
    (e : L' ≅ L) (δ : R ≅ R')
    (h : ∀ P Q (f : L'.obj P ⟶ Q),
      b.homEquiv P Q f = a.homEquiv P Q (e.inv.app P ≫ f) ≫ δ.hom.app Q) :
    conjugateIsoEquiv a b e = δ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Q
  have hh := h (R.obj Q) Q (e.hom.app _ ≫ a.counit.app Q)
  rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hh
  have hc := conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

private theorem mate_of_unit
    {L : A ⥤ B₀} {R : B₀ ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {F : A ⥤ C} {G : B₀ ⥤ D}
    (α : F ⋙ L' ⟶ L ⋙ G) (β : R ⋙ F ⟶ G ⋙ R')
    (h : ∀ P, b.homEquiv _ _ (α.app P) =
      F.map (a.unit.app P) ≫ β.app (L.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ α)) = β := by
  apply (mateEquiv a b).symm.injective
  rw [Equiv.symm_apply_apply]
  apply NatTrans.ext
  funext P
  apply (b.homEquiv _ _).injective
  change b.homEquiv _ _ (α.app P) = b.homEquiv _ _
    ((((mateEquiv a b).symm (.mk _ _ _ _ β))).app P)
  exact (h P).trans (unit_mateEquiv_symm a b (.mk _ _ _ _ β) P)

private theorem scalar_inverse_mate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (β : RA ⋙ Fm ≅ Fn ⋙ RB)
    (hc : conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ)
    (hβ : ∀ P, am.homEquiv _ _ (β.hom.app P) =
      RA.map (an.unit.app P) ≫ δ.inv.app (Fn.obj P)) :
    (mateEquiv a b (.mk _ _ _ _ γ.inv)) = β.hom := by
  apply (mateEquiv an am).injective
  have hh := iterated_mateEquiv_conjugateEquiv a b am an
    (.mk _ _ _ _ γ.inv)
  have hi : conjugateEquiv (a.comp an) (am.comp b) γ.inv = δ.inv := by
    exact congrArg Iso.inv hc
  rw [hi] at hh
  exact hh.trans (mate_of_unit an am β.hom δ.inv hβ).symm

end MateCalculus

/-- The open scalar projection mate exists and has the prescribed normalized mate.
Source: Zheng, Constructions 5.14--5.15 and Lemma 5.16; Stacks 07A4.
(blueprint: lem-pur-etale-brown-open-scalar-transport-existence).

The proof constructs the left mate of the normalized inverse-image scalar
comparison from the scalar/open adjunctions and verifies its invertibility by the
cochain localization comparison. -/
theorem etaleBrownOpenScalarTransport_exists
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
    {m n : ℕ} (h : m ≤ n) :
    ∃ op : (S.PX.scalar h).derived ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).derived,
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ op.hom)) = (S.openDerived.derivedTensor h).inv := by
  have _normalizedOpenComparison := hjo
  -- Conjugate the restriction/inverse-image isomorphism along composite adjunctions.
  let op := (conjugateIsoEquiv
    ((S.levelDerivedOpenAdjunction n).comp (S.PZ.scalar h).derivedAdj)
    ((S.PX.scalar h).derivedAdj.comp (S.levelDerivedOpenAdjunction m))).symm
      (S.openDerived.restrictedInverse h)
  -- The two normalization fields identify the other iterated mate.
  have hc := scalar_conjugate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.level n).adjunction (S.openDerived.level m).adjunction
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
    (S.openDerived.restrictedDirect_mate h)
  have hi := scalar_inverse_mate (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (S.openDerived.level n).adjunction (S.openDerived.level m).adjunction
    (S.openDerived.derivedTensor h) (S.openDerived.restrictedDirect h)
    (S.openDerived.restrictedInverse h) hc (S.openDerived.restrictedInverse_mate h)
  -- Injectivity of the scalar mate reduces the required equation to conjugation.
  refine ⟨op, ?_⟩
  apply (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj).injective
  change (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ op.hom))) =
    (mateEquiv (S.PZ.scalar h).derivedAdj (S.PX.scalar h).derivedAdj
      (.mk _ _ _ _ (S.openDerived.derivedTensor h).inv))
  rw [hi, iterated_mateEquiv_conjugateEquiv]
  exact congrArg Iso.hom ((conjugateIsoEquiv
    ((S.levelDerivedOpenAdjunction n).comp (S.PZ.scalar h).derivedAdj)
    ((S.PX.scalar h).derivedAdj.comp (S.levelDerivedOpenAdjunction m))).apply_symm_apply
      (S.openDerived.restrictedInverse h))

end AlgebraicGeometry
