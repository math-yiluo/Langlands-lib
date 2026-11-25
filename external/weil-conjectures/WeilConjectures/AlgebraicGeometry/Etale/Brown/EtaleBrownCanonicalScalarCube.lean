/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCanonicalRestrictionCube
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Scalar mate of the normalized Brown restriction cube

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

-- Normalize the mate cube before specializing to the derived categories.
private lemma mateEquiv_app_cube_converse_of_eq
    {DY DX DY' DX' EY EX EY' EX' : Type*}
    [Category* DY] [Category* DX] [Category* DY'] [Category* DX']
    [Category* EY] [Category* EX] [Category* EY'] [Category* EX']
    {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
    {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
    {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
    {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
    (σs : Gs ⋙ Mf' ⟶ Mf ⋙ Hs)
    (αf : PY ⋙ Mf ⟶ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ⟶ Lf' ⋙ PX')
    (αg : PY ⋙ Gs ⟶ Gr ⋙ PY') (αg' : PX ⋙ Hs ⟶ Hr ⋙ PX')
    (sr : Rf ⋙ Gr ⟶ Hr ⋙ Rf') (ss : Sf ⋙ Gs ⟶ Hs ⋙ Sf')
    (sf : Rf' ⋙ PY' ⟶ PX' ⋙ Sf') (sf₀ : Rf ⋙ PY ⟶ PX ⋙ Sf)
    (hσs : mateEquiv bf bf' (.mk _ _ _ _ σs) = .mk _ _ _ _ ss)
    (hαf : mateEquiv af bf (.mk _ _ _ _ αf) = .mk _ _ _ _ sf₀)
    (hαf' : mateEquiv af' bf' (.mk _ _ _ _ αf') = .mk _ _ _ _ sf)
    (h : ∀ K, αg.app (Rf.obj K) ≫ PY'.map (sr.app K) ≫ sf.app (Hr.obj K) =
      Gs.map (sf₀.app K) ≫ ss.app (PX.obj K) ≫ Sf'.map (αg'.app K)) (M : DY) :
    Mf'.map (αg.app M) ≫ αf'.app (Gr.obj M) ≫
        PX'.map (((mateEquiv af af').symm (.mk _ _ _ _ sr)).app M) =
      σs.app (PY.obj M) ≫ Hs.map (αf.app M) ≫ αg'.app (Lf.obj M) := by
  let σr := (mateEquiv af af').symm (.mk _ _ _ _ sr)
  have hσr : mateEquiv af af' σr = .mk _ _ _ _ sr :=
    (mateEquiv af af').apply_symm_apply _
  apply mateEquiv_app_cube_converse af af' bf bf' σr σs αf αf' αg αg' ?_ M
  intro K
  change αg.app (Rf.obj K) ≫ PY'.map
      ((mateEquiv af af' (.mk _ _ _ _ σr)).app K) ≫
      (mateEquiv af' bf' (.mk _ _ _ _ αf')).app (Hr.obj K) =
    Gs.map ((mateEquiv af bf (.mk _ _ _ _ αf)).app K) ≫
      (mateEquiv bf bf' (.mk _ _ _ _ σs)).app (PX.obj K) ≫ Sf'.map (αg'.app K)
  rw [hσr, hαf', hαf, hσs]
  exact h K

private lemma brown_scalarPullback_mate
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    {V W : Scheme.{u}} (g : V ⟶ W) :
    mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
        (.mk _ _ _ _ (Etale.scalarPullbackIso φ g).inv) =
      .mk _ _ _ _ (Etale.scalarRestrictionPullbackIso φ g).hom := by
  let an := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
  let av := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  have he := congrArg Iso.inv (Etale.scalarPullback_eq φ g)
  change (mateEquiv an av).symm
      (.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso φ g).hom) =
    (Etale.scalarPullbackIso φ g).inv at he
  rw [← he]
  exact (mateEquiv _ _).apply_symm_apply _

-- Share this projection: unfolding the full coherence predicate is expensive.
private lemma brown_realization_scalar_mate
    (O : Type (u + 1)) [CommRing O] (t : O) (W : Scheme.{u})
    (P : StrictEtaleEvaluation W O t) (R : StrictEtaleBrownRealization O t W P)
    {m n : ℕ} (h : m ≤ n) :
    mateEquiv (P.scalar h).derivedAdj
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h)))
        (.mk _ _ _ _ (R.scalar h).inv) = .mk _ _ _ _ (R.val.restriction h).hom :=
  R.property.2.2 h

-- Compare four independently normalized adjunctions.
/-- The scalar mate of the exact ordinary restriction square respects normalized
Brown inverse-image realizations.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-canonical-scalar-cube).

Proof: first compare ordinary restriction and inverse image in the two coefficient
encodings. After forgetting to set sheaves, the ordinary restriction comparisons
are identities; the equation for A.restrictInverseUnderlying and the ordinary
Hom-transpose equations identify the two inverse-image composites on every
section. Faithfulness of the underlying functor gives the ordinary cube. Apply
termwise cochain prolongation and exact localization. The representative equations
for the canonical restriction model, the Brown restriction comparisons, and the
assumed inverse comparison identify all four localized faces; fully faithful
precomposition by Q therefore gives the restriction cube on all derived objects.
Take the scalar-adjunction inverse mates of that cube. The scalar normalization
of RV and RW identifies their inverse mates with the displayed scalar comparisons.
The geometric restriction/pullback comparison has inverse mate scalarPullbackIso
by its canonical normalization. The inverse-mate cube identity now gives the
ordered equation below, including the exact-to-left-derived pullback comparisons.
This calculation uses no properness, finiteness or invertibility of any proper
projection mate, and works for identity maps and zero coefficient rings. -/
theorem strictEtaleBrownCanonicalScalarCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
    (hinverse : ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      letI : (strictEtaleBrownConstant O t V k).Additive := RV.val.ordinaryAdditive k
      letI : (strictEtaleBrownConstant O t W k).Additive := RW.val.ordinaryAdditive k
      letI : Functor.PreservesZeroMorphisms
          ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
        Functor.preservesZeroMorphisms_comp _ _
      (rg k).inverse.hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
          (RV.factors k).hom.app
            (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))
              (.up ℤ)).app K))
    {m n : ℕ} (h : m ≤ n) :
    let pn := (rg n).inverse.symm ≪≫ isoWhiskerLeft (RW.derived n)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).symm
    let pm := (rg m).inverse.symm ≪≫ isoWhiskerLeft (RW.derived m)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).symm
    let τ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
      (.mk _ _ _ _ (strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom))
    ∀ X : DerivedCategory (strictEtaleLevel W O t n),
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map (pn.inv.app X) ≫
          (RV.scalar h).inv.app ((B.level n).inverse.obj X) ≫
          (RV.derived m).map (τ.app X) =
        (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv.app
            ((RW.derived n).obj X) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
            g).leftDerivedFunctor.map ((RW.scalar h).inv.app X) ≫
          pm.inv.app ((PW.scalar h).derived.obj X) := by
  intro pn pm τ
  let an := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
  let av := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
  let δ := strictEtaleBrownCanonicalRestriction O t g A PW PV B h
  have hs := brown_scalarPullback_mate (strictEtaleBrownRingMap O t h) g
  have hc := strictEtaleBrownCanonicalRestrictionCube O t g A PW PV B RV RW rg hinverse h
  intro Y
  have hr : (mateEquiv (PV.scalar h).derivedAdj av
      (.mk _ _ _ _ (RV.scalar h).inv)) = .mk _ _ _ _ (RV.val.restriction h).hom :=
    brown_realization_scalar_mate O t V PV RV h
  have hw : (mateEquiv (PW.scalar h).derivedAdj an
      (.mk _ _ _ _ (RW.scalar h).inv)) = .mk _ _ _ _ (RW.val.restriction h).hom :=
    brown_realization_scalar_mate O t W PW RW h
  exact mateEquiv_app_cube_converse_of_eq
    (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj an av
    (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv
    (RW.scalar h).inv (RV.scalar h).inv pn.inv pm.inv
    δ.hom (Etale.scalarRestrictionPullbackIso (strictEtaleBrownRingMap O t h) g).hom
    (RV.val.restriction h).hom (RW.val.restriction h).hom
    hs hw hr hc Y

end AlgebraicGeometry
