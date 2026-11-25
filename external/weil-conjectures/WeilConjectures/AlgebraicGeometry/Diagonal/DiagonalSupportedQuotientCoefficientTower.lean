/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSourceQuotientNormalization
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedIntegralGeneratorSections
/-! # The supported quotient tower as a tower of additive coefficient sheaves
Source: diagonal tower system proof (3) and diagonal tower limit proof (1).
(blueprint: lem-sfb-diagonal-supported-quotient-coefficient-tower).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ comparisonUpperStar cartierUnitsComparison
  cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit
  cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierResidueReducedPro diagonalDerivedSingleCounit diagonalIntegralBoundary

private abbrev coeff (l : ℕ) [Fact l.Prime] := ULift.{u + 1} ℤ_[l]

private abbrev residueModule (l n : ℕ) [Fact l.Prime] : ModuleCat.{u + 1} (coeff l) :=
  (ModuleCat.restrictScalars (diagonalResidueProjection.{u} l n)).obj
    (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))

private abbrev residueTransition (l n : ℕ) [Fact l.Prime] :
    residueModule.{u} l (n + 1) ⟶ residueModule.{u} l n :=
  ModuleCat.ofHom (X := residueModule.{u} l (n + 1)) (Y := residueModule.{u} l n)
    { toFun := fun x ↦ ULift.up
        (ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
          (ZMod (l ^ (n + 1))) x.down)
      map_add' := by intros; apply ULift.ext; exact map_add _ _ _
      map_smul' := by
        intro a x
        apply ULift.ext
        change (ZMod.castHom _ _)
          (PadicInt.toZModPow (n + 1 + 1) a.down * x.down) =
            PadicInt.toZModPow (n + 1) a.down * _
        rw [map_mul]
        congr 1
        exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow
          (n + 1) (n + 1 + 1) (Nat.le_succ _)) a.down }

private theorem residue_compatible (l n : ℕ) [Fact l.Prime] :
    residueLinear.{u} l (n + 1) ≫ residueTransition l n = residueLinear l n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply ULift.ext
  exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow
    (n + 1) (n + 1 + 1) (Nat.le_succ _)) a.down

private abbrev constantModules (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (coeff.{u} l))

private abbrev residueTower (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    ℕᵒᵖ ⥤ DiagonalMod l X :=
  Functor.ofOpSequence (X := fun n ↦ (constantModules l X).obj (residueModule l n))
    (fun n ↦ (constantModules l X).map (residueTransition l n))

private abbrev supportedTower (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ℕᵒᵖ ⥤ DiagonalMod l (diagonalSurface Y) :=
  residueTower l (ProjectiveLine Y) ⋙ lowerStar (ModuleCat.{u + 1} (coeff l))
    (diagonalImmersion Y)

private abbrev quotientMap (l n : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    (lowerStar (ModuleCat.{u + 1} (coeff l)) (diagonalImmersion Y)).obj
        (geoCartierConstant (coeff l) (ProjectiveLine Y)) ⟶
      (supportedTower l Y).obj (op n) :=
  (lowerStar (ModuleCat.{u + 1} (coeff l)) (diagonalImmersion Y)).map
    ((constantModules l (ProjectiveLine Y)).map (residueLinear l n))

private theorem quotientMap_cokernel (l n : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    ∃ w : (l ^ (n + 1) • 𝟙 _) ≫ quotientMap l n Y = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (quotientMap l n Y) w)) := by
  let i := diagonalImmersion Y
  have : LocallyOfFinitePresentation i := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine Y ↘ Y))
    have : Smooth (ProjectiveLine Y ↘ Y) :=
      SmoothOfRelativeDimension.smooth 1 (ProjectiveLine Y ↘ Y)
    infer_instance
  let F := constantModules l (ProjectiveLine Y) ⋙
    lowerStar (ModuleCat.{u + 1} (coeff l)) i
  have : PreservesFiniteColimits
      (lowerStar (ModuleCat.{u + 1} (coeff l)) i) :=
    preservesFiniteColimits_lowerStar_of_isFinite (coeff l) i
  obtain ⟨w, ⟨h⟩⟩ := residueLinear_cokernel.{u} l n
  have hm : F.map (l ^ (n + 1) • 𝟙 (ModuleCat.of (coeff l) (coeff l))) =
      l ^ (n + 1) • 𝟙 _ := by
    rw [Functor.map_nsmul]
    exact congrArg (fun f ↦ l ^ (n + 1) • f) (F.map_id _)
  have w' : (l ^ (n + 1) • 𝟙 (F.obj _)) ≫ F.map (residueLinear l n) = 0 := by
    rw [← hm, ← F.map_comp, w, F.map_zero]
  refine ⟨w', ⟨?_⟩⟩
  change IsColimit (CokernelCofork.ofπ (F.map (residueLinear l n)) w')
  exact IsCokernel.ofIso _ (CokernelCofork.mapIsColimit _ h F)
    (CokernelCofork.ofπ _ w') (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (hm.symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem quotientMap_transition (l n : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    quotientMap l (n + 1) Y ≫
      (supportedTower l Y).map (homOfLE (Nat.le_succ n)).op = quotientMap l n Y := by
  dsimp only [quotientMap, supportedTower, Functor.comp_map]
  simp only [residueTower, Functor.ofOpSequence_map_homOfLE_succ]
  erw [← Functor.map_comp, ← Functor.map_comp, residue_compatible]

private theorem quotientTowerIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y))) :
    ∃ e : D.E.obj (diagonalIntegralSource Y) ≅ supportedTower l Y,
      ∃ a : (diagonalScalarExtension l (diagonalSurface Y)).obj
          (diagonalIntegralSource Y) ≅
        (lowerStar (ModuleCat.{u + 1} (coeff l)) (diagonalImmersion Y)).obj
          (geoCartierConstant (coeff l) (ProjectiveLine Y)),
        (∀ n, (D.π n).app (diagonalIntegralSource Y) ≫ e.hom.app (op n) =
          a.hom ≫ quotientMap l n Y) ∧
        HEq ((diagonalScalarAdjunction l (diagonalSurface Y)).unit.app _ ≫
          (diagonalForget l (diagonalSurface Y)).map a.hom)
          (cartierProIntegralGenerator (coeff l) (diagonalImmersion Y)) := by
  obtain ⟨a, ha⟩ := supported_padic_scalar_extension l (diagonalImmersion Y)
  let S := diagonalIntegralSource Y
  have hc (n : ℕ) : ∃ w : (l ^ (n + 1) • 𝟙 _) ≫
      (a.hom ≫ quotientMap l n Y) = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ (a.hom ≫ quotientMap l n Y) w)) := by
    obtain ⟨w, ⟨h⟩⟩ := quotientMap_cokernel l n Y
    have w' : (l ^ (n + 1) • 𝟙 _) ≫ (a.hom ≫ quotientMap l n Y) = 0 := by
      calc
        _ = a.hom ≫ ((l ^ (n + 1) • 𝟙 _) ≫ quotientMap l n Y) := by
          simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul, Category.id_comp]
        _ = 0 := by rw [w, comp_zero]
    refine ⟨w', ⟨?_⟩⟩
    exact IsCokernel.ofIso _ h (CokernelCofork.ofπ _ w')
      a.symm a.symm (Iso.refl _)
      (by simp only [Iso.symm_hom, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
            Category.id_comp, Category.comp_id])
      (by exact a.inv_hom_id_assoc _)
  choose w hw using hc
  let e (n : ℕ) := CokernelCofork.mapIsoOfIsColimit (D.quotient n S)
    (hw n).some (Iso.refl _)
  have he (n : ℕ) : (D.π n).app S ≫ (e n).hom = a.hom ≫ quotientMap l n Y :=
    (CokernelCofork.π_mapOfIsColimit (D.quotient n S) _ (𝟙 _)).trans
      (Category.id_comp _)
  let t : D.E.obj S ⟶ supportedTower l Y := NatTrans.ofOpSequence
    (fun n ↦ (e n).hom) (by
      intro n
      have : Epi ((D.π (n + 1)).app S) := Cofork.IsColimit.epi (D.quotient (n + 1) S)
      apply (cancel_epi ((D.π (n + 1)).app S)).mp
      rw [← Category.assoc, D.transition, he]
      rw [← Category.assoc, he, Category.assoc, quotientMap_transition])
  let ti : D.E.obj S ≅ supportedTower l Y :=
    NatIso.ofComponents (fun n ↦ e n.unop) (fun f ↦ t.naturality f)
  exact ⟨ti, a, he, ha⟩

private abbrev ringForget :=
  forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
    forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}

private abbrev ringAb (X : Scheme.{u}) :=
  sheafCompose (Scheme.ProEt.topology X) ringForget.{u}

private instance moduleForget_sheafification (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} (coeff.{u} l)) AddCommGrpCat.{u + 1}) := by
  have := (ModuleCat.forget₂CoinduceAdj (coeff.{u} l)).isLeftAdjoint
  infer_instance

private instance ringForget_sheafification (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).PreservesSheafification ringForget.{u} :=
  GrothendieckTopology.instPreservesSheafification _ _

private def residueAbIso (l n : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (residueTower l X ⋙ diagonalForget l X).obj (op n) ≅
      (Scheme.purTwistZlTower X l ⋙ ringAb X).obj (op n) :=
  (constantCommuteCompose (Scheme.ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} (coeff l)) AddCommGrpCat.{u + 1})).app
      (residueModule l n) ≪≫
    ((constantCommuteCompose (Scheme.ProEt.topology X) ringForget.{u}).app
      (CommRingCat.of (diagonalResidue.{u} l n))).symm

private theorem residueAbIso_naturality (l n : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (residueTower l X ⋙ diagonalForget l X).map (homOfLE (Nat.le_succ n)).op ≫
        (residueAbIso l n X).hom =
      (residueAbIso l (n + 1) X).hom ≫
        (Scheme.purTwistZlTower X l ⋙ ringAb X).map (homOfLE (Nat.le_succ n)).op := by
  let UM := forget₂ (ModuleCat.{u + 1} (coeff l)) AddCommGrpCat.{u + 1}
  let CM := constantCommuteCompose (Scheme.ProEt.topology X) UM
  let CR := constantCommuteCompose (Scheme.ProEt.topology X) ringForget.{u}
  let r : CommRingCat.of (diagonalResidue.{u} l (n + 1)) ⟶
      CommRingCat.of (diagonalResidue.{u} l n) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
        (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
  have hm := CM.hom.naturality (residueTransition l n)
  have hr := CR.hom.naturality r
  dsimp only [Functor.comp_map] at hm hr
  simp only [Functor.comp_map, residueTower, Scheme.purTwistZlTower,
    Scheme.purTwistZlTowerOfUniverses, Functor.ofOpSequence_map_homOfLE_succ]
  change (sheafCompose (Scheme.ProEt.topology X) UM).map
      ((constantModules l X).map (residueTransition l n)) ≫
        (CM.hom.app (residueModule l n) ≫
          CR.inv.app (CommRingCat.of (diagonalResidue.{u} l n))) =
    (CM.hom.app (residueModule l (n + 1)) ≫
      CR.inv.app (CommRingCat.of (diagonalResidue.{u} l (n + 1)))) ≫
        (sheafCompose (Scheme.ProEt.topology X) ringForget.{u}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map r)
  have hc (k : ℕ) :
      (CM.hom.app (residueModule l k) ≫
        CR.inv.app (CommRingCat.of (diagonalResidue.{u} l k))) ≫
          CR.hom.app (CommRingCat.of (diagonalResidue.{u} l k)) =
        CM.hom.app (residueModule l k) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f ↦ CM.hom.app (residueModule l k) ≫ f)
        (CR.inv_hom_id_app (CommRingCat.of (diagonalResidue.{u} l k)))).trans
          (Category.comp_id _))
  apply (cancel_mono (CR.hom.app (CommRingCat.of (diagonalResidue.{u} l n)))).mp
  refine Eq.trans ((Category.assoc _ _ _).trans (congrArg (fun f ↦
    (sheafCompose (Scheme.ProEt.topology X) UM).map
      ((constantModules l X).map (residueTransition l n)) ≫ f) (hc n))) ?_
  refine Eq.trans hm ?_
  symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f ↦ (CM.hom.app (residueModule l (n + 1)) ≫
      CR.inv.app (CommRingCat.of (diagonalResidue.{u} l (n + 1)))) ≫ f) hr).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f ↦ f ≫
            (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).map
              (ringForget.map r)) (hc (n + 1)))))

private def residueAbTowerIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    residueTower l X ⋙ diagonalForget l X ≅ Scheme.purTwistZlTower X l ⋙ ringAb X := by
  let t : residueTower l X ⋙ diagonalForget l X ⟶
      Scheme.purTwistZlTower X l ⋙ ringAb X :=
    NatTrans.ofOpSequence (fun n ↦ (residueAbIso l n X).hom)
      (residueAbIso_naturality l · X)
  exact NatIso.ofComponents (fun n ↦ residueAbIso l n.unop X) (fun f ↦ t.naturality f)

private theorem constantCommute_unit
    {C A B : Type*} [Category C] [Category A] [Category B]
    (J : GrothendieckTopology C) [HasWeakSheafify J A] [HasWeakSheafify J B]
    (U : A ⥤ B) [J.PreservesSheafification U] [J.HasSheafCompose U]
    (a : A) (V : Cᵒᵖ) :
    U.map ((toSheafify J ((Functor.const Cᵒᵖ).obj a)).app V) ≫
      ((constantCommuteCompose J U).hom.app a).hom.app V =
        (toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj a))).app V := by
  have h : Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj a)) U ≫
      ((constantCommuteCompose J U).hom.app a).hom =
        (Functor.constComp Cᵒᵖ a U).hom ≫
          toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj a)) := by
    erw [constantCommuteCompose_hom_app_hom, ← Category.assoc,
      sheafComposeIso_inv_fac, ← toSheafify_naturality]
  have hv := congr_app h V
  change U.map ((toSheafify J ((Functor.const Cᵒᵖ).obj a)).app V) ≫
    ((constantCommuteCompose J U).hom.app a).hom.app V =
      𝟙 _ ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj (U.obj a))).app V at hv
  exact hv.trans (Category.id_comp _)

private theorem residueAbIso_constants (l n : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (V : X.ProEtᵒᵖ) (a : diagonalResidue.{u} l n) :
    (residueAbIso l n X).hom.hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (residueModule l n))).app V a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (diagonalResidue.{u} l n)))).app V a := by
  let J := Scheme.ProEt.topology X
  let UM := forget₂ (ModuleCat.{u + 1} (coeff l)) AddCommGrpCat.{u + 1}
  let CR := constantCommuteCompose J ringForget.{u}
  have hm := ConcreteCategory.congr_hom
    (constantCommute_unit J UM (residueModule l n) V) a
  have hr := ConcreteCategory.congr_hom
    (constantCommute_unit J ringForget.{u}
      (CommRingCat.of (diagonalResidue.{u} l n)) V) a
  let CM := constantCommuteCompose J UM
  change (CR.inv.app (CommRingCat.of (diagonalResidue.{u} l n))).hom.app V
    ((CM.hom.app (residueModule l n)).hom.app V
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (residueModule l n))).app V a)) = _
  apply (ConcreteCategory.bijective_of_isIso
    ((CR.hom.app (CommRingCat.of (diagonalResidue.{u} l n))).hom.app V)).1
  have hi := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app V)
    (CR.inv_hom_id_app (CommRingCat.of (diagonalResidue.{u} l n))))
      ((CM.hom.app (residueModule l n)).hom.app V
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (residueModule l n))).app V a))
  exact hi.trans (hm.trans hr.symm)

private def supportedAbTowerIso (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    supportedTower l Y ⋙ diagonalForget l (diagonalSurface Y) ≅
      diagonalSupportedCoefficientTower l Y :=
  Functor.isoWhiskerRight (residueAbTowerIso l (ProjectiveLine Y))
    (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y))

private theorem quotientMap_constants (l n : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (V : X.ProEtᵒᵖ) (a : coeff.{u} l) :
    (residueAbIso l n X).hom.hom.app V
      (((constantModules l X).map (residueLinear l n)).hom.app V
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of (coeff l) (coeff l)))).app V a)) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (diagonalResidue.{u} l n)))).app V
            (diagonalResidueProjection.{u} l n a) := by
  have h := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map (residueLinear.{u} l n))) V) a
  change (residueAbIso l n X).hom.hom.app V
    (((constantModules l X).map (residueLinear l n)).hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of (coeff l) (coeff l)))).app V a)) = _
  have h' : ((constantModules l X).map (residueLinear l n)).hom.app V
      ((toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of (coeff l) (coeff l)))).app V a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (residueModule l n))).app V
          (diagonalResidueProjection.{u} l n a) := h.symm
  rw [h']
  exact residueAbIso_constants l n X V _

private theorem supportedQuotientGenerator (l n : ℕ) [Fact l.Prime] (Y : Scheme.{u}) :
    cartierProIntegralGenerator (coeff.{u} l) (diagonalImmersion Y) ≫
      (diagonalForget l (diagonalSurface Y)).map (quotientMap l n Y) ≫
        (supportedAbTowerIso l Y).hom.app (op n) =
      diagonalSupportedFiniteGenerator l Y n := by
  rw [supportedGenerator_eq]
  let X := ProjectiveLine Y
  let J := Scheme.ProEt.topology X
  let G := lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)
  change G.map (constantGenerator (coeff l) X) ≫
    G.map ((cartierForget (coeff l) X).map
      ((constantModules l X).map (residueLinear l n))) ≫
        G.map (residueAbIso l n X).hom =
    G.map (diagonalCoefficientIntegerMap X (Scheme.purTwistFiniteRing X l n))
  erw [← G.map_comp, ← G.map_comp]
  congr 1
  apply (sheafToPresheaf J AddCommGrpCat.{u + 1}).map_injective
  apply sheafify_hom_ext J _ _
    ((sheafCompose J ringForget.{u}).obj (Scheme.purTwistFiniteRing X l n)).property
  ext V z
  obtain ⟨z⟩ := z
  change (residueAbIso l n X).hom.hom.app V
    (((constantModules l X).map (residueLinear l n)).hom.app V
      ((constantGenerator (coeff l) X).hom.app V
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app V (ULift.up z)))) = _
  erw [constantGenerator_spec, quotientMap_constants]
  erw [integerMap_sections]
  rw [map_intCast]
  exact map_intCast ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
    (CommRingCat.of (diagonalResidue.{u} l n)))).app V).hom z

/-- The normalized finite cokernel comparisons assemble into an abelian tower
isomorphism. This statement involves only finite coefficients, with no completed
source object or inverse-limit comparison.

Source: blueprint latest, `sk-prop-diagonal-tower-system.proof.md`, step (3),
source paragraph, and `sk-prop-diagonal-tower-limit.proof.md`, paragraph (1).
(blueprint: lem-sfb-diagonal-supported-quotient-coefficient-tower).

Proof: the coefficient cokernel calculation and finite direct-image exactness identify
each specified quotient with the supported finite constant module with scalars restricted
along the p-adic residue projection. Forgetting scalars identifies it with the additive
sheaf of the supported finite constant ring. The constant-sheaf/forgetful comparison
preserves the sheafification unit. The normalized Cartier integral generator therefore
becomes the direct image of the integer-cast map, namely
`diagonalSupportedFiniteGenerator`. For consecutive levels, precompose the required
naturality square with D's quotient at level n+1. Both sides then become the supported
coefficient quotient map, by D.transition and the residue homomorphism equation. Cancel
this epimorphism. Consecutive naturality gives a natural transformation on the opposite
natural numbers, and the levelwise isomorphisms make it a natural isomorphism. No prime
invertibility or derived category is used; the calculation includes n=0 and empty support. -/
theorem diagonal_supported_quotient_coefficient_tower (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y))) :
    ∃ e : D.E.obj (diagonalIntegralSource Y) ⋙ diagonalForget l (diagonalSurface Y) ≅
        diagonalSupportedCoefficientTower l Y,
      ∀ n : ℕ,
        (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget l (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y)) ≫
            e.hom.app (op n) = diagonalSupportedFiniteGenerator l Y n := by
  let F := diagonalForget l (diagonalSurface Y)
  obtain ⟨e, a, he, ha⟩ := quotientTowerIso l Y D
  let t := Functor.isoWhiskerRight e F ≪≫ supportedAbTowerIso l Y
  refine ⟨t, ?_⟩
  intro n
  change (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app _ ≫
    F.map ((D.π n).app _) ≫ (F.map (e.hom.app (op n)) ≫
      (supportedAbTowerIso l Y).hom.app (op n)) = _
  have hπ : F.map ((D.π n).app (diagonalIntegralSource Y)) ≫
      F.map (e.hom.app (op n)) = F.map a.hom ≫ F.map (quotientMap l n Y) := by
    simpa only [Functor.map_comp] using congrArg F.map (he n)
  have hunit : (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app _ ≫
      F.map a.hom = cartierProIntegralGenerator (coeff l) (diagonalImmersion Y) :=
    eq_of_heq ha
  calc
    _ = ((diagonalScalarAdjunction l (diagonalSurface Y)).unit.app _ ≫
        (F.map ((D.π n).app _) ≫ F.map (e.hom.app (op n)))) ≫
          (supportedAbTowerIso l Y).hom.app (op n) := by
            simp only [Category.assoc]
    _ = (cartierProIntegralGenerator (coeff l) (diagonalImmersion Y) ≫
        F.map (quotientMap l n Y)) ≫ (supportedAbTowerIso l Y).hom.app (op n) := by
      erw [hπ, ← Category.assoc, hunit]
      rfl
    _ = _ := by
      change (cartierProIntegralGenerator (coeff l) (diagonalImmersion Y) ≫
        (diagonalForget l (diagonalSurface Y)).map (quotientMap l n Y)) ≫ _ = _
      erw [Category.assoc]
      exact supportedQuotientGenerator l n Y
end AlgebraicGeometry.ProEtale
