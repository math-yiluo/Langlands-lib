/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksData
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientRingPullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # Pulling back constant coordinates on the coefficient ring

Source: Stacks Project, Tags 00YV and 03D2.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private noncomputable def constantMap
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (k : Type (u + 1)) [CommRing k] :
    ConstantCompletion.constant J k ⟶
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
        (ConstantCompletion.constant K k) :=
  ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft F.op
      (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))))

private theorem constantMap_unit
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (k : Type (u + 1)) [CommRing k] :
    toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of k)) ≫
      (constantMap J K F k).hom =
        Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of k))) := by
  exact ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _

private theorem constantMap_pullback_isIso
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (T : C) (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) (k : Type (u + 1)) [CommRing k] :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
      CommRingCat.{u + 1} J K).homEquiv _ _).symm (constantMap J K F k)) := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    CommRingCat.{u + 1} J K
  let aJ := constantSheafAdj J CommRingCat.{u + 1} hT
  let aK := constantSheafAdj K CommRingCat.{u + 1} hFT
  let b := (aJ.comp a).ofNatIsoRight
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso CommRingCat.{u + 1} J K
      (Opposite.op T))
  have he : (a.homEquiv _ _).symm (constantMap J K F k) =
      (b.leftAdjointUniq aK).hom.app (CommRingCat.of k) := by
    apply (b.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_ofNatIsoRight_apply]
    change (aJ.comp a).homEquiv _ _
      ((a.homEquiv _ _).symm (constantMap J K F k)) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change aJ.homEquiv _ _ ((a.homEquiv _ _)
      ((a.homEquiv _ _).symm (constantMap J K F k))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj CommRingCat.{u + 1} hT).comp
      (sheafificationAdjunction J CommRingCat.{u + 1})).homEquiv _ _
        (constantMap J K F k) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj CommRingCat.{u + 1} hT).homEquiv _ _
      (((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _)
        (((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 (CommRingCat.of k) ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private theorem transportCoordinates
    {C D : Type (u + 1)} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (F : C ⥤ D) [F.IsContinuous J K] (T : C) (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) (k : Type (u + 1)) [CommRing k]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (φ : R ⟶ (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj S)
    (hφ : IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
      CommRingCat.{u + 1} J K).homEquiv _ _).symm φ))
    (c : ConstantCompletion.constant J k ≅ R) :
    ∃! d : ConstantCompletion.constant K k ≅ S,
      constantMap J K F k ≫
        (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map d.hom = c.hom ≫ φ := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    CommRingCat.{u + 1} J K
  let L := Functor.sheafPullbackConstruction.sheafPullback F CommRingCat.{u + 1} J K
  let q := (a.homEquiv _ _).symm (constantMap J K F k)
  let ψ := (a.homEquiv _ _).symm φ
  have : IsIso q := constantMap_pullback_isIso J K F T hT hFT k
  have : IsIso ψ := hφ
  let d : ConstantCompletion.constant K k ≅ S :=
    (asIso q).symm ≪≫ L.mapIso c ≪≫ asIso ψ
  have hd : q ≫ d.hom = L.map c.hom ≫ ψ := by
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv]
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have hd' : constantMap J K F k ≫
      (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map d.hom = c.hom ≫ φ := by
    have hh := congrArg (a.homEquiv _ _) hd
    change a.homEquiv _ _ (q ≫ d.hom) = a.homEquiv _ _
      ((Functor.sheafPullbackConstruction.sheafPullback F CommRingCat.{u + 1} J K).map
        c.hom ≫ ψ) at hh
    rw [a.homEquiv_naturality_right q d.hom,
      a.homEquiv_naturality_left c.hom ψ] at hh
    simpa only [q, ψ, Equiv.apply_symm_apply] using hh
  refine ⟨d, hd', ?_⟩
  intro e he
  apply Iso.ext
  apply (cancel_epi q).mp
  apply (a.homEquiv _ _).injective
  simpa only [Adjunction.homEquiv_naturality_right, q, Equiv.apply_symm_apply]
    using he.trans hd'.symm

/-- Constant coefficient coordinates extend uniquely across inverse image.
This assertion only concerns ring sheaves and their constant sections; it contains
no module equivalence, slice, or comparison of module inverse-image functors.

Source: Stacks Project, Sites, Tag 00YV (functoriality of algebraic structures),
Modules on Sites, Tag 03D2 (inverse image); coefficient transport in step 1 of
lem-sfb-constant-slice-module-encoding.
(auxiliary; not a blueprint node).

Proof: let kappa be the direct-image map extending the constant-presheaf
unit. Its ring inverse-image adjunct q is invertible: base change preserves a
terminal test object, and the constant-sheaf/global-sections adjunction shows
that both inverse-image constant functors are left adjoints to the same section
functor. Let phi be the explicit condensedSmallRingMap, and psi its adjunct,
which is invertible by condensedSmallRingMap_pullback_isIso. Define d as
q inverse, followed by inverse image of c, followed by psi. Naturality of the
adjunction gives kappa followed by direct image of d = c followed by phi.
Precomposing with the constant-presheaf unit gives the displayed section equation.
Conversely, that section equation gives the full sheaf-morphism equation by the
sheafification Hom bijection. Transpose it and cancel q to determine d.hom;
Iso.ext determines d. No nonempty-site or nonzero-ring assumption is used. -/
theorem constant_coefficient_pullback_coordinates
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X)) :
    ∃! d : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} Y) k ≅
        smallRing Y (condensedRingObj Λ Y),
      ∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
        ((InternalModuleOperations.coefficientMap Λ f).hom.app
          (AsSmall.down.op.obj V)).hom
            (c.hom.hom.app V
              ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
                ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
          d.hom.hom.app ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V)
            ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} Y)
              ((Functor.const _).obj (CommRingCat.of k))).app
                ((Scheme.coefficientProEtaleModelBaseChange.{u, u} f).op.obj V) a) := by
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, u} Y
  let F := Scheme.coefficientProEtaleModelBaseChange.{u, u} f
  let eX := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let T := eX.functor.obj (⊤_ X.ProEt)
  have hT : IsTerminal T := (terminalIsTerminal (C := X.ProEt)).isTerminalObj eX.functor
  let eY := AsSmall.equiv.{u, u + 1, u + 1} (C := Y.ProEt)
  have hFT : IsTerminal (F.obj T) :=
    ((hT.isTerminalObj eX.inverse).isTerminalObj
      (Scheme.proEtaleBaseChange f)).isTerminalObj eY.functor
  obtain ⟨d, hd, huniq⟩ := transportCoordinates J K F T hT hFT k
    (smallRing X (condensedRingObj Λ X)) (smallRing Y (condensedRingObj Λ Y))
    (condensedSmallRingMap f Λ) (condensedSmallRingMap_pullback_isIso f Λ) c
  have equivalence (e : ConstantCompletion.constant K k ≅ smallRing Y (condensedRingObj Λ Y)) :
      (∀ (V : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) (a : k),
        ((InternalModuleOperations.coefficientMap Λ f).hom.app
          (AsSmall.down.op.obj V)).hom
            (c.hom.hom.app V ((toSheafify J
              ((Functor.const _).obj (CommRingCat.of k))).app V a)) =
          e.hom.hom.app (F.op.obj V)
            ((toSheafify K ((Functor.const _).obj (CommRingCat.of k))).app (F.op.obj V) a)) ↔
        constantMap J K F k ≫
          (F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).map e.hom =
            c.hom ≫ condensedSmallRingMap f Λ := by
    constructor
    · intro he
      apply ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv _ _).injective
      change toSheafify J _ ≫ ((constantMap J K F k).hom ≫ _) =
        toSheafify J _ ≫ (c.hom.hom ≫ (condensedSmallRingMap f Λ).hom)
      rw [← Category.assoc, constantMap_unit]
      ext V a
      exact (he V a).symm
    · intro he V a
      have hh := congrArg (fun z ↦ z.hom) he
      have hh' := congrArg (fun z ↦ (toSheafify J
        ((Functor.const _).obj (CommRingCat.of k))) ≫ z) hh
      change toSheafify J _ ≫ ((constantMap J K F k).hom ≫ _) =
        toSheafify J _ ≫ (c.hom.hom ≫ (condensedSmallRingMap f Λ).hom) at hh'
      rw [← Category.assoc, constantMap_unit] at hh'
      exact (ConcreteCategory.congr_hom (NatTrans.congr_app hh' V) a).symm
  refine ⟨d, (equivalence d).mpr hd, ?_⟩
  intro e he
  exact huniq e ((equivalence e).mp he)

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
