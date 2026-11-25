/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Iso.IsoSectionwiseInverseImage
public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.Homotopy

set_option linter.privateModule false

/-! # Inverse-limit coefficient transport and scalar chain comparison

The sectionwise inverse image is the recorded canonical model for an isomorphism.
The index `op n` represents level `m = n + 1` of each inverse system.
Scalar extension uses the existing sheafified balanced tensor with the scalar first.

## References

* Stacks Project, Tag 03EL
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t r

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CochainPullback

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section AdjointSquare

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  (F : A ⥤ B) (G : C ⥤ D)
  {L : A ⥤ C} {R : C ⥤ A} {L' : B ⥤ D} {R' : D ⥤ B}
  (a : L ⊣ R) (a' : L' ⊣ R') (e : R ⋙ F ≅ G ⋙ R')

private def scalarSquareMap : F ⋙ L' ⟶ L ⋙ G where
  app M := (a'.homEquiv _ _).symm (F.map (a.unit.app M) ≫ e.hom.app (L.obj M))
  naturality {M N} f := by
    apply (a'.homEquiv _ _).injective
    change a'.homEquiv _ _ (L'.map (F.map f) ≫ _) =
      a'.homEquiv _ _ (_ ≫ G.map (L.map f))
    rw [a'.homEquiv_naturality_left, a'.homEquiv_naturality_right]
    erw [(a'.homEquiv (F.obj N) (G.obj (L.obj N))).apply_symm_apply,
      (a'.homEquiv (F.obj M) (G.obj (L.obj M))).apply_symm_apply]
    change F.map f ≫ (F.map (a.unit.app N) ≫ e.hom.app (L.obj N)) =
      (F.map (a.unit.app M) ≫ e.hom.app (L.obj M)) ≫ (G ⋙ R').map (L.map f)
    rw [Category.assoc, ← e.hom.naturality]
    change F.map f ≫ F.map (a.unit.app N) ≫ e.hom.app (L.obj N) =
      F.map (a.unit.app M) ≫ F.map (R.map (L.map f)) ≫ e.hom.app (L.obj N)
    rw [← Category.assoc, ← F.map_comp, ← Category.assoc, ← F.map_comp]
    exact congrArg (fun z ↦ F.map z ≫ e.hom.app (L.obj N)) (a.unit.naturality f)

private theorem scalarSquareMap_unit (M : A) :
    a'.unit.app (F.obj M) ≫ R'.map ((scalarSquareMap F G a a' e).app M) =
      F.map (a.unit.app M) ≫ e.hom.app (L.obj M) := by
  exact (a'.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

variable [F.IsEquivalence] [G.IsEquivalence]

private theorem scalarSquareMap_bijective (M : A) (N : C) :
    Function.Bijective (fun h : G.obj (L.obj M) ⟶ G.obj N ↦
      (scalarSquareMap F G a a' e).app M ≫ h) := by
  let E := ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
    (a.homEquiv M N)).trans
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.trans
        ((Iso.homCongr (Iso.refl (F.obj M)) (e.app N)).trans
          (a'.homEquiv (F.obj M) (G.obj N)).symm))
  have he (h : G.obj (L.obj M) ⟶ G.obj N) :
      (scalarSquareMap F G a a' e).app M ≫ h = E h := by
    apply (a'.homEquiv _ _).injective
    dsimp only [E, Equiv.trans_apply]
    erw [(a'.homEquiv (F.obj M) (G.obj N)).apply_symm_apply]
    change a'.homEquiv _ _ ((scalarSquareMap F G a a' e).app M ≫ h) =
      𝟙 _ ≫ F.map (a.homEquiv M N (G.preimage h)) ≫ e.hom.app N
    rw [Category.id_comp, a'.homEquiv_naturality_right]
    erw [(a'.homEquiv (F.obj M) (G.obj (L.obj M))).apply_symm_apply]
    change (F.map (a.unit.app M) ≫ e.hom.app (L.obj M)) ≫ R'.map h = _
    rw [a.homEquiv_unit, F.map_comp, Category.assoc, Category.assoc]
    change F.map (a.unit.app M) ≫ e.hom.app (L.obj M) ≫ R'.map h =
      F.map (a.unit.app M) ≫ (R ⋙ F).map (G.preimage h) ≫ e.hom.app N
    rw [e.hom.naturality (G.preimage h)]
    simp only [Functor.comp_map, Functor.map_preimage]
  exact (show (fun h ↦ (scalarSquareMap F G a a' e).app M ≫ h) = E from
    funext he) ▸ E.bijective

private def scalarSquareIso : F ⋙ L' ≅ L ⋙ G := by
  let b := scalarSquareMap F G a a' e
  have hb (M : A) : IsIso (b.app M) := by
    apply isIso_of_coyoneda_map_bijective
    intro T
    let i := G.asEquivalence.counitIso.app T
    let E := Iso.homCongr (Iso.refl (G.obj (L.obj M))) i
    let E' := Iso.homCongr (Iso.refl (L'.obj (F.obj M))) i
    have hh : (fun h : G.obj (L.obj M) ⟶ T ↦ b.app M ≫ h) =
        E.symm.trans ((Equiv.ofBijective _
          (scalarSquareMap_bijective F G a a' e M (G.asEquivalence.inverse.obj T))).trans
            E') := by
      funext h
      change b.app M ≫ h = 𝟙 _ ≫
        (b.app M ≫ (𝟙 _ ≫ h ≫ i.inv)) ≫ i.hom
      simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hh.symm ▸ Equiv.bijective _
  letI : ∀ M, IsIso (b.app M) := hb
  letI : IsIso b := (NatTrans.isIso_iff_isIso_app b).2 hb
  exact asIso b

private theorem scalarSquareIso_hom :
    (scalarSquareIso F G a a' e).hom = scalarSquareMap F G a a' e := rfl

private theorem scalarSquareIso_unit (M : A) :
    a'.unit.app (F.obj M) ≫ R'.map ((scalarSquareIso F G a a' e).hom.app M) =
      F.map (a.unit.app M) ≫ e.hom.app (L.obj M) := by
  rw [scalarSquareIso_hom]
  exact scalarSquareMap_unit F G a a' e M

attribute [local irreducible] scalarSquareIso

end AdjointSquare

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

-- The site equivalence is constructed once without unfolding its module adjunction.
private theorem scalarTransport_isEquivalence {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ≅ RX) :
    (SheafOfModules.pushforward.{max r (t + 1)} (F := proEtaleIsoPostcompose g)
      c.inv).IsEquivalence := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt :=
    CategoryTheory.Equivalence.mk F G e.2.1.some.symm e.2.2.1.some
  have : E.functor.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    proEtaleIsoPostcompose_isContinuous g
  have : E.inverse.IsContinuous (ProEt.topology Y) (ProEt.topology X) :=
    proEtaleIsoPostcompose_isContinuous (inv g)
  let adj := E.toAdjunction
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{max r (t + 1)})
    (ProEt.topology X) (ProEt.topology Y)
  let φ := c.inv
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c.hom
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    have hc := congrArg (fun f ↦ f.hom.app (op (G.obj U.unop))) c.hom_inv_id
    change c.hom.hom.app _ ≫ c.inv.hom.app _ = 𝟙 _ at hc
    change RY.obj.map (E.counit.app U.unop).op =
      (RY.obj.map (E.counit.app U.unop).op ≫
        c.hom.hom.app (op (G.obj U.unop))) ≫ c.inv.hom.app (op (G.obj U.unop))
    rw [Category.assoc, hc]
    exact (Category.comp_id _).symm
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c.hom]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c.hom := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c.hom := congrArg (fun h ↦ φ ≫ h ≫ c.hom) ht
        _ = _ := by
          simp only [Category.id_comp]
          exact c.inv_hom_id
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  have : (SheafOfModules.pushforward.{max r (t + 1)} (F := F) c.inv).IsEquivalence :=
    EM.isEquivalence_functor
  infer_instance

section ModuleSquare

variable {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
  {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
  (jX : RX ⟶ SX) (jY : RY ⟶ SY)
  (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
  (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX)
  (hsq : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).map jY ≫
    cS.hom = cR.hom ≫ jX)

private theorem restrictionMap_apply
    {M N : CochainPullback.Modules.{max r (t + 1), t + 1, t} SX}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((restrictionFunctor jX).map f).val.app U x = f.val.app U x := rfl

end ModuleSquare

end AlgebraicGeometry.Scheme
