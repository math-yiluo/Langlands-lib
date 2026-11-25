/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIsomorphismInverseImage
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Sectionwise inverse image along a scheme isomorphism

This is the sectionwise model of the recorded inverse image under its canonical
comma-coprojection identification. Coefficients may have any universe containing
the small site's objects; the site's object and morphism universes stay distinct.
The original site equivalence, comparison, and constant-module results are reexported.

## Main definitions and statements

- `isoSectionwiseInverseImage`: the canonical sectionwise model, with arbitrary Hom size.
- `isoSectionwiseInverseImage_equivalence`: equivalence and preservation of limits/colimits.
- `isoSectionwiseConstantMap`: coefficient transport uniquely normalized on constants.
- `isoSectionwiseModuleInverseImage`: the module action transported through the ring map.
- `isoSectionwiseModuleInverseImage_exact`: additivity and exactness of that functor.

## References

* Stacks Tags 09A5, 00WX and 0038
* Stacks Tag 0H7J
* Stacks Tags 00WX and 03D2
* Stacks Tag 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe t r d v w w'
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Postcomposition with an isomorphism preserves the topology. -/
@[instance] theorem proEtaleIsoPostcompose_isContinuous
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsContinuous (ProEt.topology X) (ProEt.topology Y) := by
  have := (proEtaleIsoPostcompose_equivalence g).1
  exact (Functor.isContinuous_iff_coverPreserving).2
    (proEtaleIsoPostcompose_equivalence g).2.2.2.1.some

/-- The sectionwise model of inverse image under the canonical site-equivalence
identification: its value at U is the original sheaf at (U, g ∘ structure). -/
abbrev isoSectionwiseInverseImage {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (D : Type d) [Category.{v} D] :
    Sheaf (ProEt.topology Y) D ⥤ Sheaf (ProEt.topology X) D :=
  (proEtaleIsoPostcompose g).sheafPushforwardContinuous D
    (ProEt.topology X) (ProEt.topology Y)

/-- The sectionwise model is an equivalence in every coefficient universe, and
preserves every existing small limit and colimit. -/
theorem isoSectionwiseInverseImage_equivalence {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (D : Type d) [Category.{v} D] :
    (isoSectionwiseInverseImage g D).IsEquivalence ∧
      PreservesLimitsOfSize.{w', w} (isoSectionwiseInverseImage g D) ∧
      PreservesColimitsOfSize.{w', w} (isoSectionwiseInverseImage g D) := by
  let F := proEtaleIsoPostcompose g
  let G := proEtaleIsoPostcompose (inv g)
  let e := proEtaleIsoPostcompose_equivalence g
  let := Functor.isContinuous_comp F G (ProEt.topology X)
    (ProEt.topology Y) (ProEt.topology X)
  let := Functor.isContinuous_comp G F (ProEt.topology Y)
    (ProEt.topology X) (ProEt.topology Y)
  let E : Sheaf (ProEt.topology Y) D ≌ Sheaf (ProEt.topology X) D :=
    CategoryTheory.Equivalence.mk (isoSectionwiseInverseImage g D)
      (isoSectionwiseInverseImage (inv g) D)
      ((Functor.sheafPushforwardContinuousComp G F D _ _ _ ≪≫
        Functor.sheafPushforwardContinuousId' e.2.2.1.some D _).symm)
      (Functor.sheafPushforwardContinuousComp F G D _ _ _ ≪≫
        Functor.sheafPushforwardContinuousId' e.2.1.some D _)
  let : (isoSectionwiseInverseImage g D).IsEquivalence := E.isEquivalence_functor
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private theorem sectionwisePostcompose_cocontinuous
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g] :
    (proEtaleIsoPostcompose g).IsCocontinuous (ProEt.topology X) (ProEt.topology Y) := by
  let e := proEtaleIsoPostcompose_equivalence g
  let E : X.ProEt ≌ Y.ProEt := CategoryTheory.Equivalence.mk
    (proEtaleIsoPostcompose g) (proEtaleIsoPostcompose (inv g))
    e.2.1.some.symm e.2.2.1.some
  exact (E.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2 e.2.2.2.2.some

private def sectionwiseConstantCommIso {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (A : CommRingCat.{max r (t + 1)}) :
    (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A) ≅
      (constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A := by
  have := sectionwisePostcompose_cocontinuous g
  exact ((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
    CommRingCat.{max r (t + 1)} (ProEt.topology X) (ProEt.topology Y)).symm.app
      ((Functor.const Y.ProEtᵒᵖ).obj A)

private theorem sectionwiseConstantCommIso_normalization
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (A : CommRingCat.{max r (t + 1)}) :
    (proEtaleIsoPostcompose g).op.whiskerLeft
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) ≫
        (sectionwiseConstantCommIso g A).hom.hom =
      toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) := by
  have := sectionwisePostcompose_cocontinuous g
  let i := (sheafToPresheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).mapIso
    (((proEtaleIsoPostcompose g).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{max r (t + 1)} (ProEt.topology X) (ProEt.topology Y)).app
        ((Functor.const Y.ProEtᵒᵖ).obj A))
  change _ ≫ i.inv = _
  apply (i.comp_inv_eq).2
  exact ((proEtaleIsoPostcompose g).toSheafify_pullbackSheafificationCompatibility
    CommRingCat.{max r (t + 1)} (ProEt.topology X) (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)).symm

/-- The constant coefficient comparison is uniquely fixed by constant sections. -/
theorem isoSectionwiseConstantMap_existsUnique {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{max r (t + 1)}) :
    ∃! c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj
        ((sheafCompose (ProEt.topology Y)
          (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A)) ⟶
        (sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{max r (t + 1)} RingCat.{max r (t + 1)})).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A),
      ∀ (U : X.ProEt) (a : A),
        c.hom.app (op U)
          ((toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app
            (op ((proEtaleIsoPostcompose g).obj U)) a) =
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app (op U) a := by
  let e := sectionwiseConstantCommIso g A
  let W := sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)
  let c := W.map e.hom
  have hn := sectionwiseConstantCommIso_normalization g A
  refine ⟨c, ?_, ?_⟩
  · intro U a
    exact congrArg (fun f ↦ (f.app (op U)) a) hn
  · intro d hd
    let d' : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj
        ((constantSheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}).obj A) ⟶
        (constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A :=
      W.preimage d
    have hmap : W.map d' = d := W.map_preimage _
    have hd' : (proEtaleIsoPostcompose g).op.whiskerLeft
        (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) ≫
        d'.hom = toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) := by
      ext U a
      have hh := hd U.unop a
      change (W.map d').hom.app U _ = _
      rw [hmap]
      exact hh
    change d = W.map e.hom
    rw [← hmap]
    apply congrArg W.map
    change d' = e.hom
    apply (cancel_epi e.inv).1
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (D := CommRingCat.{max r (t + 1)}) (ProEt.topology X) _ _
      ((constantSheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}).obj A).property
    have hni : toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) ≫
        e.inv.hom = (proEtaleIsoPostcompose g).op.whiskerLeft
          (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)) := by
      exact (((sheafToPresheaf (ProEt.topology X)
        CommRingCat.{max r (t + 1)}).mapIso e).comp_inv_eq).2 hn.symm
    change toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) ≫
        (e.inv.hom ≫ d'.hom) =
      toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A) ≫
        (e.inv.hom ≫ e.hom.hom)
    rw [← Category.assoc, ← Category.assoc, hni]
    exact hd'.trans hn.symm

/-- Constant-section coefficient transport, with no choice of an unnormalized map. -/
def isoSectionwiseConstantMap {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (A : CommRingCat.{max r (t + 1)}) :=
  (isoSectionwiseConstantMap_existsUnique g A).exists.choose

/-- The specified coefficient map is invertible. -/
@[instance] theorem isoSectionwiseConstantMap_isIso {X Y : Scheme.{t}}
    (g : X ⟶ Y) [IsIso g] (A : CommRingCat.{max r (t + 1)}) :
    IsIso (isoSectionwiseConstantMap g A) := by
  let e := sectionwiseConstantCommIso g A
  let W := sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)
  have he : isoSectionwiseConstantMap g A = W.map e.hom := by
    apply (isoSectionwiseConstantMap_existsUnique g A).unique
    · exact (isoSectionwiseConstantMap_existsUnique g A).exists.choose_spec
    · intro U a
      exact congrArg (fun f ↦ (f.app (op U)) a)
        (sectionwiseConstantCommIso_normalization g A)
  rw [he]
  infer_instance

/-- Inverse image with its action transported through the inverse coefficient map.
On sections a acts as c inverse(a); all underlying abelian groups are unchanged. -/
def isoSectionwiseModuleInverseImage {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] : SheafOfModules.{max r (t + 1)} RY ⥤
      SheafOfModules.{max r (t + 1)} RX :=
  SheafOfModules.pushforward (F := proEtaleIsoPostcompose g) (inv c)

/-- Scalar transport and site transport are additive and exact. -/
theorem isoSectionwiseModuleInverseImage_exact {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX)
    [IsIso c] :
    (isoSectionwiseModuleInverseImage g c).Additive ∧
      PreservesFiniteLimits (isoSectionwiseModuleInverseImage g c) ∧
      PreservesFiniteColimits (isoSectionwiseModuleInverseImage g c) := by
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
  let φ := inv c
  let ψ : RY ⟶ (G.sheafPushforwardContinuous RingCat _ _).obj RX :=
    shAdj.unit.app RY ≫ (G.sheafPushforwardContinuous _ _ _).map c
  have H₁ : Functor.whiskerRight (NatTrans.op E.counit) RY.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom := by
    ext U : 2
    simp [ψ, φ, shAdj, adj]
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op E.unit) RX.obj = 𝟙 RX.obj := by
    have hh : φ ≫ (E.functor.sheafPushforwardContinuous RingCat _ _).map ψ ≫
        shAdj.counit.app RX = 𝟙 RX := by
      dsimp only [ψ]
      simp only [Functor.map_comp, Category.assoc]
      erw [shAdj.counit.naturality c]
      have ht := shAdj.left_triangle_components RY
      calc
        _ = φ ≫ ((E.functor.sheafPushforwardContinuous RingCat _ _).map
            (shAdj.unit.app RY) ≫ shAdj.counit.app
              ((E.functor.sheafPushforwardContinuous RingCat _ _).obj RY)) ≫ c := by
          simp only [Category.assoc, Functor.id_map]
          rfl
        _ = φ ≫ 𝟙 _ ≫ c := congrArg (fun h ↦ φ ≫ h ≫ c) ht
        _ = _ := by simp [φ]
    exact congrArg (fun f ↦ f.hom) hh
  let EM := SheafOfModules.pushforwardPushforwardEquivalence E φ ψ H₁ H₂
  have : (isoSectionwiseModuleInverseImage g c).IsEquivalence := EM.isEquivalence_functor
  refine ⟨?_, inferInstance, inferInstance⟩
  constructor
  intro M N f h
  ext U x
  rfl

/-- Additivity supplied by the exact inverse-image theorem. -/
instance isoSectionwiseModuleInverseImage_additive {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    (isoSectionwiseModuleInverseImage g c).Additive :=
  (isoSectionwiseModuleInverseImage_exact g c).1

/-- Finite-limit preservation supplied by the exact inverse-image theorem. -/
instance isoSectionwiseModuleInverseImage_limits {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    PreservesFiniteLimits (isoSectionwiseModuleInverseImage g c) :=
  (isoSectionwiseModuleInverseImage_exact g c).2.1

/-- Finite-colimit preservation supplied by the exact inverse-image theorem. -/
instance isoSectionwiseModuleInverseImage_colimits {X Y : Scheme.{t}} (g : X ⟶ Y)
    [IsIso g] {RY : Sheaf (ProEt.topology Y) RingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) RingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g RingCat.{max r (t + 1)}).obj RY ⟶ RX) [IsIso c] :
    PreservesFiniteColimits (isoSectionwiseModuleInverseImage g c) :=
  (isoSectionwiseModuleInverseImage_exact g c).2.2

end AlgebraicGeometry.Scheme
