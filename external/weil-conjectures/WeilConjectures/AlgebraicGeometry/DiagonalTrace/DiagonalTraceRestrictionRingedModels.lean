/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import all WeilConjectures.SmoothPurity.Supporting.NativeConstantRestrictionAcyclicity
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage

/-! # Ringed-site models for the normalized diagonal scalar restriction

Source: blueprint latest, sk-prop-diagonal-tower-trace.proof.md, paragraph (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

attribute [local instance 200000] SheafOfModules.instAbelian
attribute [local instance 100000] WeilConjectures.NativeConstantModel.sequenceSmall
  WeilConjectures.NativeConstantModel.sequenceAbSheafify
  WeilConjectures.NativeConstantModel.sequenceAbLocallyBijective
  WeilConjectures.NativeConstantModel.geometricContinuous
  WeilConjectures.NativeConstantModel.siteSmall
  WeilConjectures.NativeConstantModel.siteAbSheafify
  WeilConjectures.NativeConstantModel.siteAbLocallyBijective

private def equivalenceInverseSquare
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (e : C ≌ C') (d : D ≌ D') (r : C ⥤ D) (G : C' ⥤ D')
    (a : r ⋙ d.functor ≅ e.functor ⋙ G) : e.inverse ⋙ r ≅ G ⋙ d.inverse :=
  Functor.isoWhiskerLeft e.inverse (Functor.isoWhiskerLeft r d.unitIso) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft e.inverse a) d.inverse ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight e.counitIso G) d.inverse

open WeilConjectures.NativeConstantModel in
private def constantTowerForward (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  sequenceCurry (Scheme.ProEt.topology X) (scalarRingUnderlying (Scheme.ProEt.topology X) A) ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarSectionsAt X A)

open WeilConjectures.NativeConstantModel in
private def constantTowerInverse (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ⥤
      SheafOfModules.{u + 1} (sequenceRing (Scheme.ProEt.topology X)
        (scalarRingUnderlying (Scheme.ProEt.topology X) A)) := by
  have := scalarSectionsAt_equiv X A
  exact (Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarSectionsAt X A).inv ⋙
    sequenceUncurry (Scheme.ProEt.topology X) (scalarRingUnderlying (Scheme.ProEt.topology X) A)

open WeilConjectures.NativeConstantModel in
private def constantTowerEquivalence (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    SheafOfModules.{u + 1}
        (sequenceRing (Scheme.ProEt.topology X)
          (scalarRingUnderlying (Scheme.ProEt.topology X) A)) ≌
      (ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) := by
  have := scalarSectionsAt_equiv X A
  exact (sequenceEquivalence (Scheme.ProEt.topology X)
    (scalarRingUnderlying (Scheme.ProEt.topology X) A)).trans
      (Equivalence.congrRight (E := ℕᵒᵖ) (scalarSectionsAt X A).asEquivalence)

private theorem constantTowerEquivalence_functor (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (constantTowerEquivalence X A).functor = constantTowerForward X A := rfl

private theorem constantTowerEquivalence_inverse (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    (constantTowerEquivalence X A).inverse = constantTowerInverse X A := rfl

attribute [local irreducible] constantTowerEquivalence

open WeilConjectures.NativeConstantModel in
private def constantTowerPushComparison (A : Type (u + 1)) [CommRing A]
    {X S : Scheme.{u}} (f : X ⟶ S) :
    (constantTowerEquivalence X A).inverse ⋙ sequencePush A f ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (lowerStar (ModuleCat.{u + 1} A) f) ⋙
        (constantTowerEquivalence S A).inverse := by
  let RX := scalarRing (Scheme.ProEt.topology X) A
  let RS := scalarRing (Scheme.ProEt.topology S) A
  let EX := scalarSectionsAt X A
  let ES := scalarSectionsAt S A
  have : EX.IsEquivalence := scalarSectionsAt_equiv X A
  have : ES.IsEquivalence := scalarSectionsAt_equiv S A
  let tx := Equivalence.congrRight (E := ℕᵒᵖ) EX.asEquivalence
  let ts := Equivalence.congrRight (E := ℕᵒᵖ) ES.asEquivalence
  let sx := sequenceEquivalence (Scheme.ProEt.topology X)
    (scalarRingUnderlying (Scheme.ProEt.topology X) A)
  let ss := sequenceEquivalence (Scheme.ProEt.topology S)
    (scalarRingUnderlying (Scheme.ProEt.topology S) A)
  let G := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (lowerStar (ModuleCat.{u + 1} A) f)
  let p := sequencePush A f
  let pm := AlgebraicGeometry.ProEtale.StrictTower.moduleDirectImage A f
  let gm := AlgebraicGeometry.ProEtale.StrictTower.towerDirectImage A f
  let c := Scheme.proEtaleRingDirectImageMap f RS RX
    (AlgebraicGeometry.ProEtale.StrictTower.constantRingIso A f)
  have hc : c = Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A) :=
    ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
  have hb : scalarUnit (Scheme.ProEt.topology S) A ≫
      ((sheafCompose (Scheme.ProEt.topology S)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c).hom =
        Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
          (scalarUnit (Scheme.ProEt.topology X) A) := by
    rw [hc]
    have h := Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology S) CommRingCat.{u + 1}).homEquiv
        ((Functor.const S.ProEtᵒᵖ).obj (CommRingCat.of A))
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj RX))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))))
    exact congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h
  let βm : pm ⋙ ES ≅ EX ⋙
      lowerStar (ModuleCat.{u + 1} A) f :=
    scalarDirectImageIso (Scheme.ProEt.topology X) (Scheme.ProEt.topology S)
      (Scheme.proEtaleBaseChange f) A _ _ _ _ _ hb
  let βt : gm ⋙ ts.functor ≅ tx.functor ⋙ G :=
    (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso βm
  let βti : tx.inverse ⋙ gm ≅ G ⋙ ts.inverse :=
    equivalenceInverseSquare tx ts gm G βt
  let β : (tx.inverse ⋙ sx.inverse) ⋙ p ≅ G ⋙ (ts.inverse ⋙ ss.inverse) :=
    Functor.associator tx.inverse sx.inverse p ≪≫
      Functor.isoWhiskerLeft tx.inverse (pushComparison A f) ≪≫
        (Functor.associator tx.inverse gm ss.inverse).symm ≪≫
          Functor.isoWhiskerRight βti ss.inverse ≪≫
            Functor.associator G ts.inverse ss.inverse
  exact Functor.isoWhiskerRight (eqToIso (constantTowerEquivalence_inverse X A)) p ≪≫
    β ≪≫ Functor.isoWhiskerLeft G (eqToIso (constantTowerEquivalence_inverse S A)).symm

section TowerPresentation
open WeilConjectures
open NativeConstantModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private def residueCone (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ⟶ Rrings l X :=
  NatTrans.ofOpSequence (fun n ↦
    (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (diagonalResidueProjection l n))) (by
    intro n
    simp only [Functor.const_obj_map, Rrings,
      Functor.const_obj_obj, Functor.ofOpSequence_map_homOfLE_succ, Rtransition,
      Category.id_comp, ← Functor.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext z
    change PadicInt.toZModPow (n + 1) z.down =
      ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1))) _
        (PadicInt.toZModPow (n + 2) z.down)
    exact (RingHom.congr_fun
      (PadicInt.zmod_cast_comp_toZModPow (n + 1) (n + 2) (Nat.le_succ _)) z.down).symm)

private def scalarCone (X : Scheme.{u}) :
    (Functor.const ℕᵒᵖ).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ⟶
      SemilinearSections.rings.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (fun n ↦ (Arings l E X).obj (op n))
        (fun n ↦ (Arings l E X).map (homOfLE (Nat.le_succ n)).op) :=
  NatTrans.ofOpSequence
    (fun n ↦ (residueCone l X).app (op n) ≫ SpTowerClasses.coefficientMap l E X n) (by
      intro n
      simp only [Functor.const_obj_map, SemilinearSections.rings,
        Functor.const_obj_obj, Functor.ofOpSequence_map_homOfLE_succ,
        Category.id_comp]
      change (residueCone l X).app (op n) ≫ SpTowerClasses.coefficientMap l E X n =
        ((residueCone l X).app (op (n + 1)) ≫
          SpTowerClasses.coefficientMap l E X (n + 1)) ≫ SpTowerShriek.tau l E X n
      rw [Category.assoc, coefficientMap_transition, ← Category.assoc]
      simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.id_comp] using
        congrArg (fun t ↦ t ≫ SpTowerClasses.coefficientMap l E X n)
          ((residueCone l X).naturality (homOfLE (Nat.le_succ n)).op))

private def towerScalarMap (X : Scheme.{u}) :
    sequenceCommRing (Scheme.ProEt.topology X)
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1} ℤ_[l]))) ⟶
      SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (fun n ↦ (Arings l E X).obj (op n))
        (fun n ↦ (Arings l E X).map (homOfLE (Nat.le_succ n)).op) where
  hom :=
    { app U := ((scalarCone l E X).app (op U.unop.1)).hom.app (op U.unop.2)
      naturality := by
        intro U V f
        let B := SemilinearSections.rings.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          (fun n ↦ (Arings l E X).obj (op n))
          (fun n ↦ (Arings l E X).map (homOfLE (Nat.le_succ n)).op)
        have hn := congrArg (fun t ↦ t.hom.app (op U.unop.2))
          ((scalarCone l E X).naturality f.unop.1.op)
        change ((scalarCone l E X).app (op V.unop.1)).hom.app (op U.unop.2) =
          ((scalarCone l E X).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            (B.map f.unop.1.op).hom.app (op U.unop.2) at hn
        change _ ≫ ((scalarCone l E X).app (op V.unop.1)).hom.app (op V.unop.2) =
          ((scalarCone l E X).app (op U.unop.1)).hom.app (op U.unop.2) ≫
            ((B.map f.unop.1.op).hom.app (op U.unop.2) ≫
              (B.obj (op V.unop.1)).obj.map f.unop.2.op)
        rw [← Category.assoc, ← hn]
        exact ((scalarCone l E X).app (op V.unop.1)).hom.naturality f.unop.2.op }

private def towerRestriction (X : Scheme.{u}) :
    Systems X (Arings l E X) ⥤ DiagonalSystems l X :=
  SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (towerScalarMap l E X)) ⋙
    sequenceCurry (Scheme.ProEt.topology X)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} ℤ_[l])))) ⋙
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (scalarSectionsAt X (ULift.{u + 1} ℤ_[l]))

private theorem towerRestriction_smul (X : Scheme.{u})
    (M : Systems X (Arings l E X)) (n : ℕ) (U : X.ProEtᵒᵖ)
    (z : ULift.{u + 1} ℤ_[l])
    (x : ((towerRestriction l E X).obj M).obj (op n) |>.obj.obj U) :
    z • x = ((PadicInt.toZModPow (n + 1) z.down).val : ℕ) • x := by
  let k := (PadicInt.toZModPow (n + 1) z.down).val
  let q := diagonalResidueProjection l n
  let J := Scheme.ProEt.topology X
  let cs := constantSheaf J CommRingCat.{u + 1}
  have hz : q z = (k : ULift.{u + 1} (ZMod (l ^ (n + 1)))) := by
    apply ULift.ext
    exact (ZMod.natCast_zmod_val _).symm
  have hn := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom q))) U) z
  change ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (diagonalResidue l n)))).app U).hom (q z) =
    ((cs.map (CommRingCat.ofHom q)).hom.app U).hom
      (((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app U).hom z) at hn
  have hv : (((cs.map (CommRingCat.ofHom q)).hom.app U).hom
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app U z)) =
        (k : (Rlevel l X n).obj.obj U) := by
    rw [← hn, hz, map_natCast]
  change (((SpTowerClasses.coefficientMap l E X n).hom.app U).hom
    (((cs.map (CommRingCat.ofHom q)).hom.app U).hom
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} ℤ_[l])))).app U z))) •
      (show M.val.obj (op (n, U.unop)) from x) = k • x
  rw [hv, map_natCast]
  exact Nat.cast_smul_eq_nsmul _ _ _

private theorem additive_square
    {A B A' B' : AddCommGrpCat.{u + 1}} (hA : A = A') (hB : B = B')
    (f : A →+ B) (g : A' →+ B') (h : HEq f g) :
    AddCommGrpCat.ofHom f ≫ eqToHom hB = eqToHom hA ≫ AddCommGrpCat.ofHom g := by
  subst A' B'
  cases h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private def towerRestrictionIso (X : Scheme.{u}) (rX : Restriction l E X) :
    rX.F ≅ towerRestriction l E X := by
  let e (M : Systems X (Arings l E X)) (n : ℕ) (U : X.ProEtᵒᵖ) :
      ((rX.F.obj M).obj (op n)).obj.obj U ≅
        (((towerRestriction l E X).obj M).obj (op n)).obj.obj U :=
    ModuleCat.isoMk (eqToIso (rX.underlying M n U)) (fun z ↦ by
      ext x
      change z • (show (((towerRestriction l E X).obj M).obj (op n)).obj.obj U
          from (eqToHom (rX.underlying M n U)) x) =
        (eqToHom (rX.underlying M n U))
          (z • (show ((rX.F.obj M).obj (op n)).obj.obj U from x))
      rw [towerRestriction_smul l E X, rX.scalars]
      exact (map_nsmul (eqToHom (rX.underlying M n U)).hom _ _).symm)
  refine NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun n ↦
    ObjectProperty.isoMk _ (NatIso.ofComponents (e M n.unop) ?_)) ?_) ?_
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom
      (additive_square (rX.underlying M _ U) (rX.underlying M _ V)
        _ _ (rX.restrictions M _ f)) x
  · intro m n h
    ext U x
    have hh : (homOfLE (leOfHom h.unop)).op = h := Subsingleton.elim _ _
    change _ = _
    have he := additive_square (rX.underlying M m.unop U)
      (rX.underlying M n.unop U) _ _ (rX.transitions M (leOfHom h.unop) U)
    exact ConcreteCategory.congr_hom he x
  · intro M N f
    ext n U x
    exact ConcreteCategory.congr_hom
      (additive_square (rX.underlying M _ U) (rX.underlying N _ U)
        _ _ (rX.morphisms f _ U)) x

/-- The normalized restriction and tower direct image admit simultaneous ringed-site models.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
scalar restrictions and the direct-image comparison.
(blueprint: lem-sfb-diagonal-trace-restriction-ringed-models).

Proof: map the constant integral ring to every positive residue ring by toZModPow,
then into the actual coefficient ring by coefficientMap. Compatibility gives a
ring map on the sequence site. Curry modules over the constant sequence ring,
and identify modules over the constant ring sheaf with constant-scalar module
sheaves. The five normalization equations of Restriction give the sectionwise
linear isomorphism with this functor, including restriction, transition and map
naturality. The constant direct-image structural map preserves constant sections
by the sheafification adjunction. Consequently the constant-ring equivalences
intertwine geometric direct image. Whisker this square over the sequence index,
and combine it with the explicit curry/uncurry direct-image comparison. These
are constructions of the models and both isomorphisms, with no injective or
derived-category argument. The residue action uses the first positive quotient
at n = 0; zero modules and empty sites obey the same equations. -/
theorem diagonalTrace_restriction_ringedModels {X S : Scheme.{u}} (f : X ⟶ S)
    (rX : Restriction l E X) :
    ∃ (RX : Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology X))
          CommRingCat.{u + 1})
      (RS : Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology S))
          CommRingCat.{u + 1})
      (a : RX ⟶ SemilinearSections.systemRing.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (fun n ↦ (Arings l E X).obj (op n))
        (fun n ↦ (Arings l E X).map (homOfLE (Nat.le_succ n)).op))
      (b : RS ⟶ ((ProEtale.VaryingRing.baseChange f).sheafPushforwardContinuous
        CommRingCat.{u + 1} (coefficientSequenceTopology (Scheme.ProEt.topology S))
        (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj RX)
      (eX : SheafOfModules.{u + 1}
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX) ≌ DiagonalSystems l X)
      (eS : SheafOfModules.{u + 1}
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology S))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RS) ≌ DiagonalSystems l S),
      Nonempty (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a) ⋙ eX.functor ≅ rX.F) ∧
      Nonempty (eX.inverse ⋙ SheafOfModules.pushforward.{u + 1}
        (F := ProEtale.VaryingRing.baseChange f)
        (J := coefficientSequenceTopology (Scheme.ProEt.topology S))
        (K := coefficientSequenceTopology (Scheme.ProEt.topology X))
        (R := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX)
        (S := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology S))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RS)
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology S))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map b) ≅
        diagonalTraceSystemPush l f ⋙ eS.inverse) := by
  let A := ULift.{u + 1} ℤ_[l]
  let RX := sequenceCommRing (Scheme.ProEt.topology X)
    (scalarRing (Scheme.ProEt.topology X) A)
  let RS := sequenceCommRing (Scheme.ProEt.topology S)
    (scalarRing (Scheme.ProEt.topology S) A)
  refine ⟨RX, RS, towerScalarMap l E X, geometricMap A f,
    constantTowerEquivalence X A, constantTowerEquivalence S A, ⟨?_⟩, ⟨?_⟩⟩
  · exact Functor.isoWhiskerLeft _ (eqToIso (constantTowerEquivalence_functor X A)) ≪≫
      (towerRestrictionIso l E X rX).symm
  · exact constantTowerPushComparison A f

end TowerPresentation

end AlgebraicGeometry.ProEtale.DiagonalTrace
