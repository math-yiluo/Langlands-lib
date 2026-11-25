/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownProjectionRealization
import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownRestrictionImageCube
import WeilConjectures.SmoothPurity.Supporting.EtaleBrownMateAssembly
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarMateRestrictionTranspose

/-! # The normalized proper Brown scalar transport square

Source: Zheng, Constructions 4.1 and 5.14--5.15 and Lemma 5.16;
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
private theorem brown_conjugate_transpose
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

private theorem brown_conjugate_of_transpose
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
  have hc := brown_conjugate_transpose a b e (R.obj Q) Q (a.counit.app Q)
  have hi : a.homEquiv (R.obj Q) Q (a.counit.app Q) = 𝟙 _ := by
    rw [← a.homEquiv_symm_id Q]
    exact Equiv.apply_symm_apply _ _
  rw [hi, Category.id_comp] at hh hc
  exact hc.symm.trans hh

private theorem brown_scalar_conjugate
    {TA : A ⥤ B₀} {RA : B₀ ⥤ A} (a : TA ⊣ RA)
    {TB : C ⥤ D} {RB : D ⥤ C} (b : TB ⊣ RB)
    {Fm : A ⥤ C} {Gm : C ⥤ A} (am : Fm ⊣ Gm)
    {Fn : B₀ ⥤ D} {Gn : D ⥤ B₀} (an : Fn ⊣ Gn)
    (γ : TA ⋙ Fn ≅ Fm ⋙ TB) (δ : RB ⋙ Gm ≅ Gn ⋙ RA)
    (h : ∀ P Q (f : Fn.obj (TA.obj P) ⟶ Q),
      a.homEquiv P _ (an.homEquiv _ Q f) =
        am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q) :
    conjugateIsoEquiv (am.comp b) (a.comp an) γ = δ := by
  apply brown_conjugate_of_transpose
  intro P Q f
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change a.homEquiv P _ (an.homEquiv _ Q f) =
    am.homEquiv P _ (b.homEquiv _ Q (γ.inv.app P ≫ f)) ≫ δ.hom.app Q
  exact h P Q f

end MateCalculus

private theorem mate_pasting_eval
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {LB : CB ⥤ DB} {LA' : EA ⥤ FA} {LB' : EB ⥤ FB}
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s)
    (N : CB) :
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫ V'.map (ab.app N) =
      aa.app (U.obj N) ≫ HA.map (k.app N) ≫ s.app (LB.obj N) := by
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.app N) h

-- Cancel mapped isomorphisms in small abstract categories before specialization.
private theorem rotate_right_mapped_square
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : D} (j : X ≅ Y) {Z T : C} (i : Z ≅ T)
    {U V : D} (a₁ : X ⟶ U) (a₂ : U ⟶ F.obj Z)
    (b₁ : Y ⟶ V) (b₂ : V ⟶ F.obj T)
    (h : b₁ ≫ b₂ ≫ F.map i.inv = j.inv ≫ a₁ ≫ a₂) :
    a₁ ≫ a₂ ≫ F.map i.hom = j.hom ≫ b₁ ≫ b₂ := by
  apply (cancel_epi j.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply (cancel_mono (F.map i.inv)).mp
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

set_option maxHeartbeats 8000000 in
-- Specialize mate-pasting to the concrete coefficient and sheaf derived categories.
/-- The normalized realization square for a chosen proper scalar projection.
Source: Zheng, Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-proper-scalar-square).

The proof is the mate-pasting calculation on cochain representatives. The
ordinary restriction comparison is sectionwise the identity, its derived square
is fixed by localization, and the scalar unit equation identifies the two
transposes. -/
theorem etaleBrownProperScalarSquare
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W) [IsProper g]
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ n, StrictEtaleBrownImageRealization O t g n A (B.level n) RV RW)
    {m n : ℕ} (h : m ≤ n) [Finite (strictEtaleBrownRing O t n)]
    (p : (PV.scalar h).derived ⋙ (B.level m).direct ≅
      (B.level n).direct ⋙ (PW.scalar h).derived)
    (hp : p.inv = (mateEquiv (B.level n).adjunction (B.level m).adjunction
      (.mk _ _ _ _ (B.derivedTensor h).hom))) :
    ∀ P : DerivedCategory (strictEtaleLevel V O t n),
      (RW.derived m).map (p.inv.app P) ≫
          (rg m).right.hom.app ((PV.scalar h).derived.obj P) ≫
          (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
            g).rightDerivedFunctor.map ((RV.scalar h).hom.app P) =
        (RW.scalar h).hom.app ((B.level n).direct.obj P) ≫
          (Etale.scalarExtension (strictEtaleBrownRingMap O t h) W).map
            ((rg n).right.hom.app P) ≫
          (Etale.scalarMate (strictEtaleBrownRingMap O t h) g).app
            ((RV.derived n).obj P) := by
  obtain ⟨δ, hδ, hmate⟩ :=
    Etale.scalarMate_restrictionTranspose (strictEtaleBrownRingMap O t h) g
  have hp' :
      (mateEquiv (PV.scalar h).derivedAdj (PW.scalar h).derivedAdj
        (.mk _ _ _ _ p.inv)) = (B.restrictedDirect h).hom := by
    rw [hp, iterated_mateEquiv_conjugateEquiv]
    exact congrArg Iso.hom (brown_scalar_conjugate
      (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
      (B.level n).adjunction (B.level m).adjunction
      (B.derivedTensor h) (B.restrictedDirect h) (B.restrictedDirect_mate h))
  intro P
  have hcube := etaleBrownMatePasting
    (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)))
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h)))
    (.mk _ _ _ _ (RW.scalar h).inv) (.mk _ _ _ _ (RV.scalar h).inv)
    (.mk _ _ _ _ p.inv)
    (.mk _ _ _ _ (Etale.scalarMate (strictEtaleBrownRingMap O t h) g))
    (rg n).right.hom (rg m).right.hom
    (by
      intro M
      rw [congr_app (RV.property.2.2 h) M,
        congr_app (RW.property.2.2 h) ((B.level m).direct.obj M),
        congr_app hp' M, congr_app hmate ((RV.derived m).obj M)]
      exact etaleBrownRestrictionImageCube O t g A PW PV B RV RW rg h δ hδ M)
  have hh := mate_pasting_eval
    (.mk _ _ _ _ (RW.scalar h).inv) (.mk _ _ _ _ (RV.scalar h).inv)
    (.mk _ _ _ _ p.inv)
    (.mk _ _ _ _ (Etale.scalarMate (strictEtaleBrownRingMap O t h) g))
    (rg n).right.hom (rg m).right.hom hcube P
  exact rotate_right_mapped_square
    (Etale.lowerStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
      g).rightDerivedFunctor
    ((RW.scalar h).app ((B.level n).direct.obj P)) ((RV.scalar h).app P)
    ((RW.derived m).map (p.inv.app P))
    ((rg m).right.hom.app ((PV.scalar h).derived.obj P))
    ((Etale.scalarExtension (strictEtaleBrownRingMap O t h) W).map
      ((rg n).right.hom.app P))
    ((Etale.scalarMate (strictEtaleBrownRingMap O t h) g).app
      ((RV.derived n).obj P)) hh

end AlgebraicGeometry
