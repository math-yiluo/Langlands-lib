/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement

/-!
# Inverse image along an object of the small pro-etale site is slice restriction

The private comparison data live in
`WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement`.

## References

* Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J
* Modules on Sites, Tags 03D2 and 03EK
* Tag 09A5
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Restriction of constant-coefficient modules through the constant-ring localization
isomorphism `e: A_W ≅ A_X|_W`. This is the existing sectionwise pushforward of
module sheaves along composition; its scalar action uses `e.hom` and its underlying
abelian presheaf is exactly `U ↦ M(U → W → X)`. -/
noncomputable abbrev proEtaleObjectModuleRestriction {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A)) :=
  letI : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  SheafOfModules.pushforward.{u + 1} (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing W.left A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionCoefficientMap {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] :
    proEtaleCoefficientInverseImageMap (X := W.left) (Y := X) W.hom A ≫
      (restrictionConstantIso W A).hom =
      (restrictionComparison W CommRingCat.{u + 1}).sheafIso.hom.app
        (proEtaleConstantRing X A) := by
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing W.left A
  let c := restrictionComparison W CommRingCat.{u + 1}
  let e := restrictionConstantIso W A
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  let g := proEtaleCoefficientInverseImageMap (X := W.left) (Y := X) W.hom A
  have hg :
      (proEtaleSheafAdjunction (X := W.left) (Y := X) W.hom CommRingCat.{u + 1}).unit.app R ≫
      (proEtaleSheafDirectImage (X := W.left) (Y := X) W.hom CommRingCat.{u + 1}).map g =
      proEtaleCoefficientDirectImageMap (X := W.left) (Y := X) W.hom A := by
    exact ((proEtaleSheafAdjunction (X := W.left) (Y := X) W.hom
      CommRingCat.{u + 1}).homEquiv R S).apply_symm_apply
      (proEtaleCoefficientDirectImageMap (X := W.left) (Y := X) W.hom A)
  have h : e.hom ≫ c.sheafIso.inv.app R ≫ g = 𝟙 S := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology W.left) _ _ S.property
    apply NatTrans.ext
    funext U
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    rw [← Category.assoc, ← Category.assoc, restrictionConstantIso_unit]
    rw [c.sheafIso_inv]
    dsimp only [NatTrans.comp_app]
    rw [c.coprojection]
    let k := (proEtaleObjectInverseImageIndexPoint W U.unop).hom.op
    have hn := (toSheafify (ProEt.topology W.left)
      ((proEtaleBaseChange W.hom).op.lan.obj R.obj) ≫ g.hom).naturality k
    have hu := congrArg (fun z ↦ z.hom.app (op (F.obj U.unop))) hg
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
    rw [inverseImageAdjunction_unit] at hu
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
    have hρ := ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
        ((proEtaleSheafDirectImage (X := W.left) (Y := X) W.hom
          CommRingCat.{u + 1}).obj S)).apply_symm_apply
        (Functor.whiskerLeft (proEtaleBaseChange W.hom).op
          (toSheafify (ProEt.topology W.left)
            ((Functor.const W.left.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))))
    have hρU := congrArg (fun z ↦ z.app (op (F.obj U.unop))) hρ
    rw [Adjunction.homEquiv_unit] at hρU
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hρU
    change (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (F.obj U.unop)) ≫
      (((proEtaleBaseChange W.hom).op.lanUnit.app R.obj).app (op (F.obj U.unop)) ≫
        ((proEtaleBaseChange W.hom).op.lan.obj R.obj).map k) ≫
      (toSheafify (ProEt.topology W.left)
        ((proEtaleBaseChange W.hom).op.lan.obj R.obj)).app U ≫ g.hom.app U = _
    dsimp only [NatTrans.comp_app] at hn
    simp only [Category.assoc] at hn hu ⊢
    erw [hn]
    have hu' := congrArg (fun z ↦
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (F.obj U.unop)) ≫ z ≫ S.obj.map k) hu
    have hρ' := congrArg (fun z ↦ z ≫ S.obj.map k) hρU
    apply Eq.trans (by
      simpa [S, F, proEtaleObjectInverseImageIndexPoint, proEtaleSheafDirectImage,
        AlgebraicGeometry.ProEtale.lowerStar, Category.assoc] using hu')
    apply Eq.trans (by
      simpa [S, F, proEtaleCoefficientDirectImageMap, proEtaleConstantDirectImageMap,
        Category.assoc] using hρ')
    have ht := (toSheafify (ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality k
    calc
      _ = (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app U := by
          simpa [S, F, proEtaleObjectInverseImageIndexPoint,
            proEtaleConstantRing, constantSheaf] using ht.symm
      _ = _ := (Category.comp_id _).symm
  change g ≫ e.hom = c.sheafIso.hom.app R
  apply (cancel_epi (c.sheafIso.inv.app R)).mp
  apply (cancel_epi e.hom).mp
  have hh := congrArg (fun z ↦ z ≫ e.hom) h
  simp only [Category.assoc] at hh ⊢
  calc
    e.hom ≫ c.sheafIso.inv.app R ≫ g ≫ e.hom = 𝟙 S ≫ e.hom := hh
    _ = e.hom := Category.id_comp _
    _ = e.hom ≫ c.sheafIso.inv.app R ≫ c.sheafIso.hom.app R := by
      rw [c.sheafIso.inv_hom_id_app]
      exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionModulePullback {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap W.hom A)]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
  let : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  let P := SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing W.left A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
∃ rho : ∀ M : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)),
          proEtaleConstantModulePullback W.hom A M ≅
            P.obj M,
        ∀ (M N : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))
          (a : M ⟶ N),
          proEtaleConstantModulePullbackMap W.hom A a ≫ (rho N).hom =
            (rho M).hom ≫ P.map a := by
  let : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  let : (proEtaleBaseChange W.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology W.left) :=
    ProEt.isContinuous_overPullback W.hom
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing W.left A
  let c := asIso (proEtaleCoefficientInverseImageMap W.hom A)
  have hψ : proEtaleRingDirectImageMap W.hom R S c =
      proEtaleCoefficientDirectImageMap W.hom A := by
    exact ((proEtaleSheafAdjunction W.hom CommRingCat.{u + 1}).homEquiv R S).apply_symm_apply
      (proEtaleCoefficientDirectImageMap W.hom A)
  let φ : ((sheafCompose (ProEt.topology W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ⟶
      ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology W.left) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((proEtaleBaseChange W.hom).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology X) (ProEt.topology W.left)).obj
        ((sheafCompose (ProEt.topology W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap W.hom A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom :=
    coefficient_restriction_counit W A e he
  have H₂ := coefficient_restriction_unit W A e he
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁)
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂)
  let b := proEtaleRingModuleAdjunction W.hom R S c
  have hD : proEtaleRingModuleDirectImage W.hom R S c =
      SheafOfModules.pushforward.{u + 1} ψ := by
    unfold proEtaleRingModuleDirectImage
    rw [hψ]
  rw [hD] at b
  let i := b.leftAdjointUniq a
  refine ⟨fun M ↦ i.app M, ?_⟩
  intro M N f
  exact i.hom.naturality f

/-- Inverse image along an object is slice restriction, including the canonical
presheaf comparison, the sheafification unit, the particular coefficient map, and
module pullback. The commutative-ring comparison retains the ring structure needed
for coefficients; `RingCat` also includes noncommutative ring sheaves. -/
theorem proEtaleObjectInverseImageRestriction (X : Scheme.{u}) (W : X.ProEt)
    (A : Type u) [CommRing A] :
    (∀ U : W.left.ProEt,
      Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint W U))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W (Type (u + 1))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W AddCommGrpCat.{u + 1}) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W RingCat.{u + 1}) ∧
    ∃ (comparison : ProEtaleObjectRestrictionComparison W CommRingCat.{u + 1})
      (e : proEtaleConstantRing W.left A ≅
        (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
          W.hom W.prop).obj (proEtaleConstantRing X A)),
      (∀ U : W.left.ProEt,
        (toSheafify (ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app
                (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) ∧
      proEtaleCoefficientInverseImageMap W.hom A ≫ e.hom =
        comparison.sheafIso.hom.app (proEtaleConstantRing X A) ∧
      ∃ rho : ∀ M : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)),
          proEtaleConstantModulePullback W.hom A M ≅
            (proEtaleObjectModuleRestriction W A e).obj M,
        ∀ (M N : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))
          (a : M ⟶ N),
          proEtaleConstantModulePullbackMap W.hom A a ≫ (rho N).hom =
            (rho M).hom ≫ (proEtaleObjectModuleRestriction W A e).map a := by
  refine ⟨?_, ⟨restrictionComparison W (Type (u + 1))⟩,
    ⟨restrictionComparison W AddCommGrpCat.{u + 1}⟩,
    ⟨restrictionComparison W RingCat.{u + 1}⟩, ?_⟩
  · intro U
    classical
    let adj := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial)
    let lift : ∀ b : proEtaleInverseImageIndex W.hom U,
        proEtaleObjectInverseImageIndexPoint W U ⟶ b := fun b ↦
      StructuredArrow.homMk ((adj.homEquiv U b.right).symm b.hom) (by
        exact (adj.homEquiv_unit _ _ _).symm.trans
          ((adj.homEquiv U b.right).apply_symm_apply b.hom))
    refine ⟨IsInitial.ofUniqueHom lift (fun b f ↦ ?_)⟩
    apply StructuredArrow.hom_ext
    apply (adj.homEquiv U b.right).injective
    rw [Adjunction.homEquiv_unit]
    exact (StructuredArrow.w f).trans
      ((adj.homEquiv U b.right).apply_symm_apply b.hom).symm
  · have : IsIso (proEtaleCoefficientInverseImageMap W.hom A) := by
      apply (isIso_comp_right_iff (proEtaleCoefficientInverseImageMap W.hom A)
        (restrictionConstantIso W A).hom).mp
      rw [restrictionCoefficientMap W A]
      infer_instance
    refine ⟨restrictionComparison W CommRingCat.{u + 1}, restrictionConstantIso W A,
      restrictionConstantIso_unit W A, restrictionCoefficientMap W A, ?_⟩
    exact restrictionModulePullback W A (restrictionConstantIso W A)
      (restrictionConstantIso_unit W A)

end AlgebraicGeometry.Scheme
