/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarDerivedComparison
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenScalarSupport
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.SemilinearProperOpenNormalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Scalar compatibility of the intrinsic inverse-image clopen word

## References

* Stacks Project, Tag 0F7B, open case
* Zheng, Construction 4.1 and Lemma 4.10
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 64
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
open Normalization
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

section NormalizedComparison
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryFactors Functor.rightDerivedFunctor HasDerivedCategory.standard
  constantSheaf DerivedCategory.Q rhoOrdinary alpha gamma
  WeilConjectures.SemilinearSections.systemRing coefficientMap VaryingRing.ringMap
attribute [local implicit_reducible] VaryingRing.ordinaryScalarMap
  VaryingRing.coefficientTransition
attribute [local instance] VaryingRing.push_isRightAdjoint VaryingRing.push_additive
  VaryingRing.pullAdditive VaryingRing.pullLimits VaryingRing.pullColimits
attribute [local instance] rho_additive rho_limits rho_colimits

/-- Localize a section-normalized identification of the ordinary scalar functors. -/
private def localized_scalar_iso
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n))) (X : Scheme.{u})
    (a : D.rho X ≅ rhoOrdinary C τ B φ hφ X) :
    VaryingRing.scalarRho D X ≅ rho C τ B φ hφ X := by
  let rA : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
  let rL : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
  let rC : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
  let dA : (D.rho X).Additive := D.additive X
  let dL : PreservesFiniteLimits (D.rho X) := D.limits X
  let dC : PreservesFiniteColimits (D.rho X) := D.colimits X
  exact Functor.mapDerivedCategoryNatIso a

/-- Identity on sections identifies the chosen direct-image square and hence its mate. -/
private theorem normalized_pull
    (D : VaryingRing.OrdinaryScalarComparison C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
    (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y)
    (haX : ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
      (x : (((D.rho X).obj M).obj (op n)).val.obj H),
      HEq (((aX.hom.app M).app (op n)).val.app H x) x)
    (haY : ∀ (M : Modules C τ Y) (n : ℕ) (H : Y.ProEtᵒᵖ)
      (x : (((D.rho Y).obj M).obj (op n)).val.obj H),
      HEq (((aY.hom.app M).app (op n)).val.app H x) x)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (Scheme.proEtaleBaseChange f).obj U)) ↦ x)) :
    HEq ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ e.inv))
      (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
        (D.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  subst F
  let d := Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY.symm ≪≫
    D.d f ≪≫ Functor.isoWhiskerRight aX (StrictTower.towerDirectImage B f)
  have hd : d.hom = e.inv := by
    apply (cancel_mono e.hom).mp
    erw [e.inv_hom_id]
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    let y := (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) x
    let z := ((((D.d f).hom.app M).app n).val.app U) y
    let t := (((aX.hom.app M).app n).val.app
      ((Scheme.proEtaleBaseChange f).op.obj U)) z
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aY.hom.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ congrArg (fun v ↦ (v.app n).val.app U q)
        (aY.inv_hom_id_app ((VaryingRing.push C τ f).obj M)))
      (haY ((VaryingRing.push C τ f).obj M) n.unop U) x
    have hz := D.d_sections f M n.unop U y
    have ht := haX M n.unop ((Scheme.proEtaleBaseChange f).op.obj U) z
    have hh := normalized_apply
      (rho_section_type C τ B φ hφ X M n.unop
        ((Scheme.proEtaleBaseChange f).obj U.unop))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n.unop U.unop)
      _ (he M n.unop U.unop) t
    exact eq_of_heq (hh.trans (ht.trans (hz.trans hy)))
  let w := ((TwoSquare.mk _ _ _ _ (D.b f).inv).whiskerTop aY.inv).whiskerBottom aX.hom
  have hw : mateEquiv (VaryingRing.moduleAdj C τ f)
      (VaryingRing.scalarTowerAdj B f) w = TwoSquare.mk _ _ _ _ d.hom := by
    dsimp only [w]
    erw [mateEquiv_whiskerTop_whiskerBottom]
    refine NatTrans.ext (funext fun N ↦ ?_)
    change aY.inv.app ((VaryingRing.push C τ f).obj N) ≫
      (mateEquiv (VaryingRing.moduleAdj C τ f) (VaryingRing.scalarTowerAdj B f)
        (D.b f).inv).app N ≫
        (StrictTower.towerDirectImage B f).map (aX.hom.app N) = d.hom.app N
    rw [D.mate]
    rfl
  rw [← hd]
  change HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
    (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ d.hom)) _
  rw [← hw, Equiv.symm_apply_apply]
  exact HEq.rfl

attribute [local irreducible] rhoP VaryingRing.scalarB VaryingRing.scalarA

attribute [local irreducible] P J StrictTower.G StrictTower.J
  StrictTower.alpha VaryingRing.alpha localized_scalar_iso

private theorem app_heq
    {A B : Type*} [Category A] [Category B]
    {F F' G G' : A ⥤ B} (a : F ⟶ G) (b : F' ⟶ G')
    (hF : F = F') (hG : G = G') (hab : HEq a b) {M N : A} (hM : M = N) :
    HEq (a.app M) (b.app N) := by
  subst F' G' N
  cases hab
  rfl

private theorem map_heq
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {M M' N N' : A} (f : M ⟶ N) (g : M' ⟶ N')
    (hM : M = M') (hN : N = N') (hfg : HEq f g) : HEq (F.map f) (F.map g) := by
  subst M' N'
  cases hfg
  rfl

private theorem composition_heq
    {C : Type*} [Category C] {A A' B B' D D' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') (g : B ⟶ D) (g' : B' ⟶ D')
    (hA : A = A') (hB : B = B') (hD : D = D') (hf : HEq f f') (hg : HEq g g') :
    HEq (f ≫ g) (f' ≫ g') := by
  subst A' B' D'
  cases hf
  cases hg
  rfl


end NormalizedComparison

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
