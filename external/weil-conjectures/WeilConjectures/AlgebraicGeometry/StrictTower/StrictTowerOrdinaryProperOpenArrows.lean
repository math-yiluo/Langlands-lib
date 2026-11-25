/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
public import WeilConjectures.CategoryTheory.SmoothPurity.TermwiseCompositeTransformation
public import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
public import WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows

/-! # Ordinary clopen arrows for constant-coefficient strict towers

Source: Stacks Project, Tags 09BN, 0F7B, and the underived refinement of the blueprint.
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows)

These are the ordinary constructions underlying the recorded derived arrows. All
functors and adjunctions are the already specified constant-ring module operations.
The open unit, its direct-image transpose, and the clopen projector are imported
from ProperOpenClopenProjector. Cartesian beta and the open-extension compositor
are imported from TowerOpenBetaNormalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback

/-- Unit-preserving open-adjoint transport along equality of scheme morphisms.
Source: Stacks, Tag 09BN
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleJCongr {U X : Scheme.{u}} {f g : U ⟶ X}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) : moduleJ B f ≅ moduleJ B g :=
  ((moduleJAdj B f).ofNatIsoRight
    (eqToIso (congrArg (modulePullback B) h))).leftAdjointUniq (moduleJAdj B g)

/-- The intrinsic ordinary alpha: cartesian beta, clopen projection, and compositors.
Source: Stacks, Tag 0F7B and the blueprint's underived refinement
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def singleAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : moduleJ B i ⋙ modulePullback B p ⟶
      modulePullback B r ⋙ moduleJ B k :=
  (openBetaModule B (pullback.snd p i) (pullback.fst p i) i p
    (pullback.condition.symm) (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (modulePullback B (pullback.snd p i))
    (clopenModulePi B (squareLift k r p i h))) (moduleJ B (pullback.fst p i)) ≫
  Functor.whiskerRight
    (Functor.associator (modulePullback B (pullback.snd p i))
      (modulePullback B (squareLift k r p i h)) (moduleJ B (squareLift k r p i h))).inv
      (moduleJ B (pullback.fst p i)) ≫
  (Functor.associator
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    (moduleJ B (squareLift k r p i h)) (moduleJ B (pullback.fst p i))).hom ≫
  Functor.whiskerLeft
    (modulePullback B (pullback.snd p i) ⋙ modulePullback B (squareLift k r p i h))
    ((openBetaModuleJComp B (squareLift k r p i h) (pullback.fst p i)).hom ≫
      (singleJCongr B (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight
    ((moduleGComp B (squareLift k r p i h) (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).hom) (moduleJ B k)

/-- Termwise alpha on strict towers, before taking complexes.
Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows). -/
def towerAlpha {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : towerJ B i ⋙ towerPullback B p ⟶
      towerPullback B r ⋙ towerJ B k :=
  Functor.termwiseCompositeTransformation ℕᵒᵖ (Modules B S) (Modules B T)
    (Modules B V) (Modules B W) (moduleJ B i) (modulePullback B p)
    (modulePullback B r) (moduleJ B k) (singleAlpha B k r p i h)

section DescentCalculus

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v₁ v₂ v₃ u₁ u₂ u₃ w₁ w₂ w₃
variable {A : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} A] [Category.{v₂} D] [Category.{v₃} E]
  [aA : Abelian A] [aD : Abelian D] [aE : Abelian E]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} D]
  [HasDerivedCategory.{w₃} E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] clopenTowerAbelian

private abbrev ordinaryAbelian (X : Scheme.{u}) : Abelian (Modules B X) :=
  @SheafOfModules.instAbelian.{u + 1, u, u + 1, u + 1} _ _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X))
    (SheafOfModules.hasSheafify_coefficientUniverse.{u + 1, u, u + 1})
    (SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1})

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem adjCongr_refl {L : A ⥤ D} {R : D ⥤ A} (a : L ⊣ R) :
    ((a.ofNatIsoRight (Iso.refl R)).leftAdjointUniq a).hom = 𝟙 L := by
  have he : a.ofNatIsoRight (Iso.refl R) = a := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext X
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app]
    exact Category.comp_id _
  rw [he, Adjunction.leftAdjointUniq_refl]

private theorem singleJCongr_refl {U X : Scheme.{u}} (f : U ⟶ X)
    [IsOpenImmersion f] : (singleJCongr B (rfl : f = f)).hom = 𝟙 _ := by
  exact adjCongr_refl (moduleJAdj B f)

private def compCompatible
    (F : A ⥤ D) (H : D ⥤ E) (L : A ⥤ E) [F.Additive] [H.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ⟶ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶ L.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫ L.mapDerivedCategoryFactors.hom.app K =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K)

private def squareCompatible
    {C : Type*} [Category C] [aC : Abelian C] [HasDerivedCategory C]
    (F : A ⥤ D) (H : D ⥤ E) (G : A ⥤ C) (L : C ⥤ E)
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ⟶ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶
      G.mapDerivedCategory ⋙ L.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K)

private def unitCompatible (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory) : Prop :=
  ∀ K : CochainComplex A ℤ,
    d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K)

private theorem factorsh_eq (F : A ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app, Iso.refl_hom, Iso.refl_inv, Functor.comp_obj]
  erw [F.mapDerivedCategory.map_id, Category.id_comp, DerivedCategory.Qh.map_id,
    Category.comp_id, Category.comp_id]

private theorem exact_unit_fac
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [Abelian.HasKInjectiveResolutions D] (a : L ⊣ R)
    (K : CochainComplex A ℤ) :
    (exactAdj a).unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  have h := exactAdj_unit a ((HomotopyCategory.quotient A (.up ℤ)).obj K)
  rw [factorsh_eq] at h
  change (exactAdj a).unit.app (DerivedCategory.Q.obj K) ≫
    R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient D (.up ℤ)).obj
          ((L.mapHomologicalComplex (.up ℤ)).obj K)) = _ at h
  rw [factorsh_eq, Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  exact h

private theorem hom_fac
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (d : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hu : ∀ K : CochainComplex A ℤ,
      d.unit.app (DerivedCategory.Q.obj K) ≫
          R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
          R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K))
    (K : CochainComplex A ℤ) (N : CochainComplex D ℤ)
    (f : (L.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    d.homEquiv _ _ (L.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R.mapDerivedCategoryFactors.inv.app N := by
  apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app N)).1
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality,
    ← Category.assoc (R.mapDerivedCategory.map _)]
  rw [← Category.assoc, hu]
  simp only [Iso.inv_hom_id_app, ← Functor.map_comp]
  erw [Category.comp_id]
  rw [Adjunction.homEquiv_unit]

private theorem comp_hom_fac
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (K : CochainComplex A ℤ) (N : CochainComplex E ℤ)
    (f : ((L₁ ⋙ L₂).mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    ((exactAdj a).comp (exactAdj b)).homEquiv _ _
        (L₂.mapDerivedCategory.map (L₁.mapDerivedCategoryFactors.hom.app K) ≫
          L₂.mapDerivedCategoryFactors.hom.app
            ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (((a.comp b).mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        R₁.mapDerivedCategoryFactors.inv.app ((R₂.mapHomologicalComplex (.up ℤ)).obj N) ≫
        R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.inv.app N) := by
  rw [Adjunction.comp_homEquiv]
  change (exactAdj a).homEquiv _ _ ((exactAdj b).homEquiv _ _ _) = _
  erw [Adjunction.homEquiv_naturality_left,
    hom_fac b (exactAdj b) (exact_unit_fac b)]
  erw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [hom_fac a (exactAdj a) (exact_unit_fac a)]
  simp only [Category.assoc]
  congr 2
  ext n
  simp [Adjunction.homEquiv_unit, Adjunction.comp_unit_app]

omit [Abelian A] [Abelian D] [HasDerivedCategory A] [HasDerivedCategory D] in
private theorem conjugate_hom_fac
    {L L' : A ⥤ D} {R R' : D ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ≅ L')
    (K : A) (N : D) (f : L'.obj K ⟶ N) :
    a.homEquiv K N (e.hom.app K ≫ f) =
      b.homEquiv K N f ≫ (conjugateIsoEquiv b a e).hom.app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp]
  have h := unit_conjugateEquiv b a e.hom K
  dsimp only [conjugateIsoEquiv_apply_hom] at *
  rw [← Category.assoc, ← h, Category.assoc]
  simpa only [Category.assoc] using
    congrArg (b.unit.app K ≫ ·) ((conjugateEquiv b a e.hom).naturality f).symm
private theorem comp_iso_fac
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : A ⥤ E} {R₃ : E ⥤ A}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [L₃.Additive] [R₃.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits L₃] [PreservesFiniteColimits L₃]
    [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions E]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃)
    (e : R₂ ⋙ R₁ ≅ R₃) (K : CochainComplex A ℤ) :
    (Adjunction.leftAdjointCompIso (exactAdj a) (exactAdj b) (exactAdj c)
      ((Functor.mapDerivedCategoryCompIso R₂ R₁) ≪≫
        Functor.mapDerivedCategoryNatIso e)).hom.app (DerivedCategory.Q.obj K) ≫
        L₃.mapDerivedCategoryFactors.hom.app K =
      L₂.mapDerivedCategory.map (L₁.mapDerivedCategoryFactors.hom.app K) ≫
        L₂.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (Adjunction.leftAdjointCompIso a b c e).hom (.up ℤ)).app K) := by
  let l := Adjunction.leftAdjointCompIso a b c e
  let r := (Functor.mapDerivedCategoryCompIso R₂ R₁) ≪≫
    Functor.mapDerivedCategoryNatIso e
  let ld := Adjunction.leftAdjointCompIso (exactAdj a) (exactAdj b) (exactAdj c) r
  apply (((exactAdj a).comp (exactAdj b)).homEquiv _ _).injective
  have hd : conjugateIsoEquiv (exactAdj c) ((exactAdj a).comp (exactAdj b)) ld = r.symm := by
    simp [ld, Adjunction.leftAdjointCompIso]
  have hc : (((a.comp b).mapHomologicalComplex (.up ℤ)).homEquiv _ _
      ((NatTrans.mapHomologicalComplex l.hom (.up ℤ)).app K)) =
        (c.mapHomologicalComplex (.up ℤ)).unit.app K ≫
          (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app
            ((L₃.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext n
    have h := unit_conjugateEquiv c (a.comp b) l.hom (K.X n)
    have he : conjugateEquiv c (a.comp b) l.hom = e.inv := by
      simp [l, Adjunction.leftAdjointCompIso]
    rw [he] at h
    simpa [Adjunction.homEquiv_unit, Adjunction.comp_unit_app] using h.symm
  change ((exactAdj a).comp (exactAdj b)).homEquiv _ _
    (ld.hom.app _ ≫ L₃.mapDerivedCategoryFactors.hom.app K) = _
  have hf := hom_fac c (exactAdj c) (exact_unit_fac c) K
    ((L₃.mapHomologicalComplex (.up ℤ)).obj K) (𝟙 _)
  erw [DerivedCategory.Q.map_id, Category.comp_id, Adjunction.homEquiv_id] at hf
  rw [conjugate_hom_fac, hd, Iso.symm_hom]
  erw [hf]
  erw [comp_hom_fac, hc]
  apply (cancel_mono
    (R₁.mapDerivedCategory.map (R₂.mapDerivedCategoryFactors.hom.app
      ((L₃.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      R₁.mapDerivedCategoryFactors.hom.app
        ((R₂.mapHomologicalComplex (.up ℤ)).obj
          ((L₃.mapHomologicalComplex (.up ℤ)).obj K)))).1
  have hi := Functor.mapDerivedCategoryNatIso_fac e.symm
    ((L₃.mapHomologicalComplex (.up ℤ)).obj K)
  rw [Functor.mapDerivedCategoryNatIso_symm] at hi
  dsimp only [r, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  simp only [Category.assoc, Functor.map_comp]
  have hcomp := Functor.mapDerivedCategoryCompIso_hom_app_factors R₂ R₁
    ((L₃.mapHomologicalComplex (.up ℤ)).obj K)
  erw [hcomp, hi]
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  simp only [Category.assoc, ← R₁.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [R₁.mapDerivedCategory.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app]
  erw [Category.id_comp, Category.comp_id]
  rfl

private theorem compNat_fac
    {F : A ⥤ D} {H : D ⥤ E} {L : A ⥤ E}
    [F.Additive] [H.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ L) (K : CochainComplex A ℤ) :
    ((Functor.mapDerivedCategoryCompIso F H) ≪≫
      Functor.mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategoryFactors.hom.app K =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc]
  have ht := Functor.mapDerivedCategoryCompIso_hom_app_factors F H K
  rw [← ht]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem compNat_fac_of_eq
    {F : A ⥤ D} {H : D ⥤ E} {L : A ⥤ E}
    [F.Additive] [H.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ L) (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ L.mapDerivedCategory)
    (hd : d = (Functor.mapDerivedCategoryCompIso F H) ≪≫
      Functor.mapDerivedCategoryNatIso e) (K : CochainComplex A ℤ) :
    d.hom.app (DerivedCategory.Q.obj K) ≫ L.mapDerivedCategoryFactors.hom.app K =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  subst d
  exact compNat_fac e K

private theorem square_fac
    {F : A ⥤ D} {H : D ⥤ E} {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {G : A ⥤ C} {L : C ⥤ E}
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ G ⋙ L) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc]
  have ht := Functor.mapDerivedCategoryCompIso_hom_app_factors F H K
  rw [← ht]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

private theorem square_fac_of_eq
    {F : A ⥤ D} {H : D ⥤ E} {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {G : A ⥤ C} {L : C ⥤ E}
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (e : F ⋙ H ≅ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ G.mapDerivedCategory ⋙ L.mapDerivedCategory)
    (hd : d = Functor.mapDerivedCategorySquareIso e) (K : CochainComplex A ℤ) :
    d.hom.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  subst d
  exact square_fac e K

private theorem squareCompatible_of_eq
    {C : Type*} [Category C] [aC : Abelian C] [HasDerivedCategory C]
    (F : A ⥤ D) (H : D ⥤ E) (G : A ⥤ C) (L : C ⥤ E)
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ≅ G ⋙ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ L.mapDerivedCategory)
    (hd : d = Functor.mapDerivedCategorySquareIso t) :
    squareCompatible F H G L t.hom d.hom := by
  intro K
  exact square_fac_of_eq t d hd K

private theorem compCompatible_of_eq
    (F : A ⥤ D) (H : D ⥤ E) (L : A ⥤ E) [F.Additive] [H.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ≅ L)
    (d : F.mapDerivedCategory ⋙ H.mapDerivedCategory ≅ L.mapDerivedCategory)
    (hd : d = (Functor.mapDerivedCategoryCompIso F H) ≪≫
      Functor.mapDerivedCategoryNatIso t) : compCompatible F H L t.hom d.hom := by
  intro K
  exact compNat_fac_of_eq t d hd K


omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem whisker_comp_hom
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : A ⥤ E} {R₃ : E ⥤ A}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (e : R₃ ≅ R₂ ⋙ R₁) :
    (Adjunction.leftAdjointCompIso (a.whiskerRight ℕᵒᵖ) (b.whiskerRight ℕᵒᵖ)
      (c.whiskerRight ℕᵒᵖ)
      (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso e) ≪≫
        Functor.whiskeringRightObjCompIso R₂ R₁).symm).hom =
      ((Functor.whiskeringRightObjCompIso L₁ L₂).symm ≪≫
        (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
          (Adjunction.leftAdjointCompIso a b c e.symm)).hom := by
  ext M n
  simp only [Adjunction.leftAdjointCompIso_hom_app]
  dsimp only [Functor.whiskeringRight, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.whiskeringRightObjCompIso,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  simp only [Adjunction.whiskerRight_unit_app_app,
    Adjunction.whiskerRight_counit_app_app, Category.comp_id, Category.id_comp,
    Adjunction.leftAdjointCompIso_hom_app]
  rfl

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
@[irreducible] private def termwiseCompHom (f : A ⥤ D) (g : D ⥤ E) (h : A ⥤ E)
    (t : f ⋙ g ⟶ h) :
    (Functor.whiskeringRight ℕᵒᵖ A D).obj f ⋙
      (Functor.whiskeringRight ℕᵒᵖ D E).obj g ⟶
      (Functor.whiskeringRight ℕᵒᵖ A E).obj h :=
  (Functor.whiskeringRightObjCompIso f g).inv ≫
    (Functor.whiskeringRight ℕᵒᵖ A E).map t

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private abbrev tw {C D : Type*} [Category C] [Category D] (f : C ⥤ D) :=
  (Functor.whiskeringRight ℕᵒᵖ C D).obj f

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem whisker_exact_comp_fac
    [hA : HasDerivedCategory (ℕᵒᵖ ⥤ A)] [hD : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [hE : HasDerivedCategory (ℕᵒᵖ ⥤ E)]
    [kiD : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ D)]
    [kiE : Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ E)]
    {L₁ : A ⥤ D} {R₁ : D ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L₃ : A ⥤ E} {R₃ : E ⥤ A}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [L₃.Additive] [R₃.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits L₃] [PreservesFiniteColimits L₃]
    [PreservesFiniteLimits R₃] [PreservesFiniteColimits R₃]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (e : R₃ ≅ R₂ ⋙ R₁)
    (d₁ : (tw L₁).mapDerivedCategory ⊣ (tw R₁).mapDerivedCategory)
    (d₂ : (tw L₂).mapDerivedCategory ⊣ (tw R₂).mapDerivedCategory)
    (d₃ : (tw L₃).mapDerivedCategory ⊣ (tw R₃).mapDerivedCategory)
    (de : (tw R₂).mapDerivedCategory ⋙ (tw R₁).mapDerivedCategory ≅
      (tw R₃).mapDerivedCategory)
    (h₁ : exactAdj (a.whiskerRight ℕᵒᵖ) = d₁)
    (h₂ : exactAdj (b.whiskerRight ℕᵒᵖ) = d₂)
    (h₃ : exactAdj (c.whiskerRight ℕᵒᵖ) = d₃)
    (he : de = (Functor.mapDerivedCategoryCompIso (tw R₂) (tw R₁)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (((Functor.whiskeringRight ℕᵒᵖ E A).mapIso e) ≪≫
          Functor.whiskeringRightObjCompIso R₂ R₁).symm)
    (τ : L₁ ⋙ L₂ ⟶ L₃)
    (δ : (tw L₁).mapDerivedCategory ⋙ (tw L₂).mapDerivedCategory ⟶
      (tw L₃).mapDerivedCategory)
    (hτ : τ = (Adjunction.leftAdjointCompIso a b c e.symm).hom)
    (hδ : δ = (Adjunction.leftAdjointCompIso d₁ d₂ d₃ de).hom)
    : compCompatible (tw L₁) (tw L₂) (tw L₃)
      (termwiseCompHom L₁ L₂ L₃ τ) δ := by
  intro K
  subst τ δ d₁ d₂ d₃ de
  have hf := comp_iso_fac (a.whiskerRight ℕᵒᵖ) (b.whiskerRight ℕᵒᵖ)
    (c.whiskerRight ℕᵒᵖ)
    (((Functor.whiskeringRight ℕᵒᵖ E A).mapIso e) ≪≫
      Functor.whiskeringRightObjCompIso R₂ R₁).symm K
  rw [whisker_comp_hom] at hf
  simpa only [termwiseCompHom, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using hf

set_option backward.isDefEq.respectTransparency true in
private theorem jComp_fac {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    : compCompatible (aA := clopenTowerAbelian B U)
      (aD := clopenTowerAbelian B V) (aE := clopenTowerAbelian B X)
      (towerJ B j) (towerJ B k) (towerJ B (j ≫ k))
      (termwiseCompHom (moduleJ B j) (moduleJ B k) (moduleJ B (j ≫ k))
        (openBetaModuleJComp B j k).hom) (jComp B j k).hom := by
  have hr : (gComp B j k).symm =
      (Functor.mapDerivedCategoryCompIso (towerPullback B k)
        (towerPullback B j)) ≪≫
      Functor.mapDerivedCategoryNatIso (towerGComp B j k).symm := by
    apply Iso.ext
    simp only [gComp, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Functor.mapDerivedCategoryNatIso_symm]
    rfl
  exact whisker_exact_comp_fac (A := Modules B U) (D := Modules B V) (E := Modules B X)
    (aA := ordinaryAbelian B U) (aD := ordinaryAbelian B V) (aE := ordinaryAbelian B X)
    (hA := towers_hasDerivedCategory B U) (hD := towers_hasDerivedCategory B V)
    (hE := towers_hasDerivedCategory B X)
    (kiD := towers_kInjective B V) (kiE := towers_kInjective B X)
    (L₁ := moduleJ B j) (R₁ := modulePullback B j)
    (L₂ := moduleJ B k) (R₂ := modulePullback B k)
    (L₃ := moduleJ B (j ≫ k)) (R₃ := modulePullback B (j ≫ k))
    (moduleJAdj B j) (moduleJAdj B k)
    (moduleJAdj B (j ≫ k)) (moduleGComp B j k)
    (jAdj B j) (jAdj B k) (jAdj B (j ≫ k)) (gComp B j k).symm
    (exactAdj_jAdj B j) (exactAdj_jAdj B k) (exactAdj_jAdj B (j ≫ k)) hr
    (openBetaModuleJComp B j k).hom (jComp B j k).hom rfl rfl

private theorem pair_fac (F : A ⥤ D) (H : D ⥤ E) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryCompIso F H).hom.app (DerivedCategory.Q.obj K) ≫
        (F ⋙ H).mapDerivedCategoryFactors.hom.app K =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F H).inv.app _)).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  simpa only [Category.assoc] using
    (Functor.mapDerivedCategoryCompIso_hom_app_factors F H K).symm

private theorem pair_descent
    {F : A ⥤ D} {H : D ⥤ E} {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {G : A ⥤ C} {L : C ⥤ E}
    [F.Additive] [H.Additive] [G.Additive] [L.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (t : F ⋙ H ⟶ G ⋙ L)
    (a : F.mapDerivedCategory ⋙ H.mapDerivedCategory ⟶
      G.mapDerivedCategory ⋙ L.mapDerivedCategory)
    (ha : ∀ K : CochainComplex A ℤ,
      a.app (DerivedCategory.Q.obj K) ≫
        L.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app K) ≫
        L.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K)) :
    ClopenProjectorDescent (F ⋙ H) (G ⋙ L) t
      ((Functor.mapDerivedCategoryCompIso F H).inv ≫ a ≫
        (Functor.mapDerivedCategoryCompIso G L).hom) := by
  intro K
  dsimp only [NatTrans.comp_app]
  simp only [Category.assoc]
  rw [pair_fac, ha]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

private theorem beta_fac {U' U X' X : Scheme.{u}}
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (g : X' ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion j'] (w : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) :
    squareCompatible (aA := clopenTowerAbelian B U)
      (aD := clopenTowerAbelian B X) (aE := clopenTowerAbelian B X')
      (aC := clopenTowerAbelian B U')
      (towerJ B j) (towerPullback B g) (towerPullback B a) (towerJ B j')
      (openBetaTower B a j' j g w sq).hom (beta B a j' j g w sq).hom := by
  have hn := (openBetaNormalization B a j' j g w sq).1
  change beta B a j' j g w sq = Functor.mapDerivedCategorySquareIso
    (openBetaTower B a j' j g w sq) at hn
  exact squareCompatible_of_eq (towerJ B j) (towerPullback B g)
    (towerPullback B a) (towerJ B j')
    (openBetaTower B a j' j g w sq) (beta B a j' j g w sq) hn

private theorem idDescent_pair_fac
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (p : 𝟭 A ⟶ F ⋙ H) (d : 𝟭 (DerivedCategory A) ⟶
      F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hd : ClopenProjectorDescent (𝟭 A) (F ⋙ H) p
      ((Functor.mapDerivedCategoryIdIso A).hom ≫ d ≫
        (Functor.mapDerivedCategoryCompIso F H).hom))
    (K : CochainComplex A ℤ) :
    d.app (DerivedCategory.Q.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex p (.up ℤ)).app K) := by
  have hp := hd K
  dsimp only [NatTrans.comp_app] at hp
  simp only [Category.assoc] at hp
  rw [pair_fac] at hp
  have hi : (Functor.mapDerivedCategoryIdIso A).hom.app
      (DerivedCategory.Q.obj K) = (𝟭 A).mapDerivedCategoryFactors.hom.app K := by
    rw [← factorsh_eq]
    exact Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj _ _
  rw [hi] at hp
  exact (cancel_epi ((𝟭 A).mapDerivedCategoryFactors.hom.app K)).1 hp

private theorem unitCompatible_of_descent
    (F : A ⥤ D) (H : D ⥤ A) [F.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (p : 𝟭 A ⟶ F ⋙ H)
    (d : 𝟭 (DerivedCategory A) ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hd : ClopenProjectorDescent (𝟭 A) (F ⋙ H) p
      ((Functor.mapDerivedCategoryIdIso A).hom ≫ d ≫
        (Functor.mapDerivedCategoryCompIso F H).hom)) : unitCompatible F H p d := by
  intro K
  exact idDescent_pair_fac F H p d hd K

private theorem pi_fac {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) :
    unitCompatible (aA := clopenTowerAbelian B X) (aD := clopenTowerAbelian B U)
      (towerPullback B s) (towerJ B s) (clopenTowerPi B s) (pi B s) := by
  exact unitCompatible_of_descent (towerPullback B s) (towerJ B s)
    (clopenTowerPi B s) (pi B s) (clopenDerived_section_projector B s c hc).1

private theorem gComp_fac {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    : compCompatible (aA := clopenTowerAbelian B Z)
      (aD := clopenTowerAbelian B Y) (aE := clopenTowerAbelian B X)
      (towerPullback B g) (towerPullback B f) (towerPullback B (f ≫ g))
      (towerGComp B f g).inv (gComp B f g).inv := by
  have he : (gComp B f g).symm =
      (Functor.mapDerivedCategoryCompIso (towerPullback B g) (towerPullback B f)) ≪≫
        Functor.mapDerivedCategoryNatIso (towerGComp B f g).symm := by
    apply Iso.ext
    simp only [gComp, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm]
  exact compCompatible_of_eq (towerPullback B g) (towerPullback B f)
    (towerPullback B (f ≫ g)) (towerGComp B f g).symm (gComp B f g).symm he

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem projector_paste (G : A ⥤ D) (J : D ⥤ A) (H : A ⥤ E) (L : D ⥤ E)
    (p : 𝟭 A ⟶ G ⋙ J) (a : J ⋙ H ⟶ L)
    {x x' z : A} {y : D} {w v : E}
    (f : x ⟶ x') (g : G.obj x' ⟶ y) (l : J.obj y ⟶ z)
    (m : H.obj z ⟶ w) (n : w ⟶ v) (t : L.obj y ⟶ v)
    (ha : a.app y ≫ t = H.map l ≫ m ≫ n)
    (p' : x' ⟶ z) (hp : p.app x' ≫ J.map g ≫ l = p') :
    H.map (p.app x) ≫ a.app (G.obj x) ≫ L.map (G.map f) ≫ L.map g ≫ t =
      H.map f ≫ H.map p' ≫ m ≫ n := by
  have hc : p.app x ≫ J.map (G.map f ≫ g) ≫ l = f ≫ p' := by
    rw [J.map_comp]
    rw [← Category.assoc, ← Category.assoc]
    change ((p.app x ≫ (G ⋙ J).map f) ≫ J.map g) ≫ l = _
    rw [← p.naturality f]
    simpa only [Category.assoc, Functor.id_map, Functor.id_obj] using congrArg (f ≫ ·) hp
  calc
    _ = H.map (p.app x ≫ J.map (G.map f ≫ g) ≫ l) ≫ m ≫ n := by
      rw [← L.map_comp_assoc, ← a.naturality_assoc]
      change H.map (p.app x) ≫ H.map (J.map (G.map f ≫ g)) ≫ a.app y ≫ t = _
      rw [ha]
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by rw [hc, H.map_comp]; simp only [Category.assoc]

private def towerJTail {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    (l : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (h : j ≫ k = l) : towerJ B j ⋙ towerJ B k ⟶ towerJ B l :=
  termwiseCompHom (moduleJ B j) (moduleJ B k) (moduleJ B l)
    ((openBetaModuleJComp B j k).hom ≫ (singleJCongr B h).hom)

private def towerGTail {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) (h : f ≫ g = r) :
    towerPullback B g ⋙ towerPullback B f ⟶ towerPullback B r :=
  termwiseCompHom (modulePullback B g) (modulePullback B f) (modulePullback B r)
    ((moduleGComp B f g).inv ≫ (eqToIso (congrArg (modulePullback B) h)).hom)

private theorem jTail_fac {U V X : Scheme.{u}} (j : U ⟶ V) (k : V ⟶ X)
    (l : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (h : j ≫ k = l) :
    compCompatible (aA := clopenTowerAbelian B U)
      (aD := clopenTowerAbelian B V) (aE := clopenTowerAbelian B X)
      (towerJ B j) (towerJ B k) (towerJ B l) (towerJTail B j k l h)
      ((jComp B j k).hom ≫ (jCongr B h).hom) := by
  subst l
  simp only [jCongr, eqToIso_refl, Iso.refl_hom, Category.comp_id, towerJTail,
    singleJCongr_refl]
  exact jComp_fac B j k

private theorem gTail_fac {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : X ⟶ Z) (h : f ≫ g = r) :
    compCompatible (aA := clopenTowerAbelian B Z)
      (aD := clopenTowerAbelian B Y) (aE := clopenTowerAbelian B X)
      (towerPullback B g) (towerPullback B f) (towerPullback B r)
      (towerGTail B f g r h)
      ((gComp B f g).inv ≫ (eqToIso (congrArg (G B) h)).hom) := by
  subst r
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id, towerGTail, termwiseCompHom]
  simpa only [towerGComp, Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp,
    Functor.map_id, Category.comp_id] using gComp_fac B f g

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_four
    {F₀ F₁ F₂ F₃ F₄ : A ⥤ E}
    [F₀.Additive] [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
    (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂) (c : F₂ ⟶ F₃) (d : F₃ ⟶ F₄)
    (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (a ≫ b ≫ c ≫ d) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex a (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex b (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex c (.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex d (.up ℤ)).app K := by
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_whiskerLeft
    (F : A ⥤ D) {H L : D ⥤ E} [F.Additive] [H.Additive] [L.Additive]
    (a : H ⟶ L) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft F a) (.up ℤ)).app K =
      (NatTrans.mapHomologicalComplex a (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n
  rfl

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_whiskerRight
    {F G : A ⥤ D} (H : D ⥤ E) [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex (Functor.whiskerRight a H) (.up ℤ)).app K =
      (H.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  ext n
  rfl

private theorem localization_paste
    {C T : Type*} [Category C] [Category T] [aC : Abelian C] [aT : Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory T]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    [i.Additive] [p.Additive] [q.Additive] [s.Additive] [j.Additive]
    [b.Additive] [k.Additive] [r.Additive]
    [PreservesFiniteLimits i] [PreservesFiniteColimits i]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits j] [PreservesFiniteColimits j]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits k] [PreservesFiniteColimits k]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r)
    (β : i.mapDerivedCategory ⋙ p.mapDerivedCategory ⟶
      q.mapDerivedCategory ⋙ b.mapDerivedCategory)
    (π : 𝟭 (DerivedCategory D) ⟶ s.mapDerivedCategory ⋙ j.mapDerivedCategory)
    (a : j.mapDerivedCategory ⋙ b.mapDerivedCategory ⟶ k.mapDerivedCategory)
    (e : q.mapDerivedCategory ⋙ s.mapDerivedCategory ⟶ r.mapDerivedCategory)
    (hβ : squareCompatible i p q b βt β)
    (hπ : unitCompatible s j pt π)
    (ha : compCompatible j b k τj a)
    (he : compCompatible q s r et e) :
    ClopenProjectorDescent (i ⋙ p) (r ⋙ k)
      (βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
        Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k)
      ((Functor.mapDerivedCategoryCompIso i p).inv ≫
        (β ≫ Functor.whiskerRight (Functor.whiskerLeft q.mapDerivedCategory π)
          b.mapDerivedCategory ≫
        Functor.whiskerLeft (q.mapDerivedCategory ⋙ s.mapDerivedCategory) a ≫
        Functor.whiskerRight e k.mapDerivedCategory) ≫
        (Functor.mapDerivedCategoryCompIso r k).hom) := by
  apply pair_descent
  intro K
  let M := (q.mapHomologicalComplex (.up ℤ)).obj K
  let N := (s.mapHomologicalComplex (.up ℤ)).obj M
  let pt' := (NatTrans.mapHomologicalComplex pt (.up ℤ)).app M
  let τj' := (NatTrans.mapHomologicalComplex τj (.up ℤ)).app N
  let et' := (NatTrans.mapHomologicalComplex et (.up ℤ)).app K
  have hgt : k.mapDerivedCategory.map (e.app (DerivedCategory.Q.obj K)) ≫
      k.mapDerivedCategory.map (r.mapDerivedCategoryFactors.hom.app K) ≫
      k.mapDerivedCategoryFactors.hom.app ((r.mapHomologicalComplex (.up ℤ)).obj K) =
      k.mapDerivedCategory.map
        (s.mapDerivedCategory.map (q.mapDerivedCategoryFactors.hom.app K)) ≫
      k.mapDerivedCategory.map (s.mapDerivedCategoryFactors.hom.app M) ≫
      k.mapDerivedCategoryFactors.hom.app N ≫
      DerivedCategory.Q.map ((k.mapHomologicalComplex (.up ℤ)).map et') := by
    rw [← k.mapDerivedCategory.map_comp_assoc, he]
    simp only [Functor.map_comp, Category.assoc]
    erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  have hpaste := projector_paste s.mapDerivedCategory j.mapDerivedCategory
    b.mapDerivedCategory k.mapDerivedCategory π a
    (q.mapDerivedCategoryFactors.hom.app K) (s.mapDerivedCategoryFactors.hom.app M)
    (j.mapDerivedCategoryFactors.hom.app N)
    (b.mapDerivedCategoryFactors.hom.app ((j.mapHomologicalComplex (.up ℤ)).obj N))
    (DerivedCategory.Q.map τj') (k.mapDerivedCategoryFactors.hom.app N)
    (ha N) (DerivedCategory.Q.map pt') (hπ M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  rw [hgt]
  erw [reassoc_of% hpaste]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality_assoc]
  erw [reassoc_of% hβ K]
  simp only [complex_four, complex_whiskerLeft, complex_whiskerRight,
    Functor.map_comp]
  rfl

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem whisker_paste
    {C T : Type*} [Category C] [Category T]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r) :
    (Functor.whiskeringRightObjCompIso i p).hom ≫
      (Functor.whiskeringRight ℕᵒᵖ A E).map
        (βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
          Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k) ≫
      (Functor.whiskeringRightObjCompIso r k).inv =
    ((Functor.whiskeringRightObjCompIso i p).hom ≫
      (Functor.whiskeringRight ℕᵒᵖ A E).map βt ≫
      (Functor.whiskeringRightObjCompIso q b).inv) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft ((Functor.whiskeringRight ℕᵒᵖ A D).obj q)
        ((Functor.whiskeringRight ℕᵒᵖ D D).map pt))
      ((Functor.whiskeringRight ℕᵒᵖ D E).obj b) ≫
    Functor.whiskerLeft
      ((Functor.whiskeringRight ℕᵒᵖ A D).obj q ⋙
        (Functor.whiskeringRight ℕᵒᵖ D C).obj s)
      ((Functor.whiskeringRightObjCompIso j b).inv ≫
        (Functor.whiskeringRight ℕᵒᵖ C E).map τj) ≫
    Functor.whiskerRight
      ((Functor.whiskeringRightObjCompIso q s).inv ≫
        (Functor.whiskeringRight ℕᵒᵖ A C).map et)
      ((Functor.whiskeringRight ℕᵒᵖ C E).obj k) := by
  ext M n
  dsimp only [Functor.whiskeringRightObjCompIso, Functor.whiskeringRight,
    towerJ, towerPullback,
    Functor.comp_obj, Functor.comp_map, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, NatTrans.comp_app, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  simp only [Category.id_comp, Category.comp_id]

omit [Abelian A] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem assoc_paste
    {C T : Type*} [Category C] [Category T]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r) :
    βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
      Functor.whiskerRight (Functor.associator q s j).inv b ≫
      (Functor.associator (q ⋙ s) j b).hom ≫
      Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k =
    βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
      Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.comp_obj,
    Category.id_comp]
  rw [b.map_id, Category.id_comp]

omit [HasDerivedCategory A] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem module_localization_paste
    {C T : Type*} [Category C] [Category T] [aC : Abelian C] [aT : Abelian T]
    [hA : HasDerivedCategory (ℕᵒᵖ ⥤ A)] [hD : HasDerivedCategory (ℕᵒᵖ ⥤ D)]
    [hE : HasDerivedCategory (ℕᵒᵖ ⥤ E)] [hC : HasDerivedCategory (ℕᵒᵖ ⥤ C)]
    [hT : HasDerivedCategory (ℕᵒᵖ ⥤ T)]
    (i : A ⥤ T) (p : T ⥤ E) (q : A ⥤ D) (s : D ⥤ C) (j : C ⥤ D)
    (b : D ⥤ E) (k : C ⥤ E) (r : A ⥤ C)
    [i.Additive] [p.Additive] [q.Additive] [s.Additive] [j.Additive]
    [b.Additive] [k.Additive] [r.Additive]
    [PreservesFiniteLimits i] [PreservesFiniteColimits i]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits j] [PreservesFiniteColimits j]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    [PreservesFiniteLimits k] [PreservesFiniteColimits k]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (βt : i ⋙ p ⟶ q ⋙ b) (pt : 𝟭 D ⟶ s ⋙ j) (τj : j ⋙ b ⟶ k)
    (et : q ⋙ s ⟶ r)
    (β : (tw i).mapDerivedCategory ⋙ (tw p).mapDerivedCategory ⟶
      (tw q).mapDerivedCategory ⋙ (tw b).mapDerivedCategory)
    (π : 𝟭 (DerivedCategory (ℕᵒᵖ ⥤ D)) ⟶ (tw s).mapDerivedCategory ⋙ (tw j).mapDerivedCategory)
    (a : (tw j).mapDerivedCategory ⋙ (tw b).mapDerivedCategory ⟶ (tw k).mapDerivedCategory)
    (e : (tw q).mapDerivedCategory ⋙ (tw s).mapDerivedCategory ⟶ (tw r).mapDerivedCategory)
    (hβ : squareCompatible (tw i) (tw p) (tw q) (tw b)
      (Functor.termwiseCompositeTransformation ℕᵒᵖ A T D E i p q b βt) β)
    (hπ : unitCompatible (tw s) (tw j)
      ((Functor.whiskeringRight ℕᵒᵖ D D).map pt) π)
    (ha : compCompatible (tw j) (tw b) (tw k) (termwiseCompHom j b k τj) a)
    (he : compCompatible (tw q) (tw s) (tw r) (termwiseCompHom q s r et) e) :
    ClopenProjectorDescent (tw i ⋙ tw p) (tw r ⋙ tw k)
      (Functor.termwiseCompositeTransformation ℕᵒᵖ A T C E i p r k
        (βt ≫ Functor.whiskerRight (Functor.whiskerLeft q pt) b ≫
          Functor.whiskerRight (Functor.associator q s j).inv b ≫
          (Functor.associator (q ⋙ s) j b).hom ≫
          Functor.whiskerLeft (q ⋙ s) τj ≫ Functor.whiskerRight et k))
      ((Functor.mapDerivedCategoryCompIso (tw i) (tw p)).inv ≫
        (β ≫ Functor.whiskerRight (Functor.whiskerLeft (tw q).mapDerivedCategory π)
          (tw b).mapDerivedCategory ≫
        Functor.whiskerRight
          (Functor.associator (tw q).mapDerivedCategory (tw s).mapDerivedCategory
            (tw j).mapDerivedCategory).inv (tw b).mapDerivedCategory ≫
        (Functor.associator ((tw q).mapDerivedCategory ⋙ (tw s).mapDerivedCategory)
          (tw j).mapDerivedCategory (tw b).mapDerivedCategory).hom ≫
        Functor.whiskerLeft ((tw q).mapDerivedCategory ⋙ (tw s).mapDerivedCategory) a ≫
        Functor.whiskerRight e (tw k).mapDerivedCategory) ≫
        (Functor.mapDerivedCategoryCompIso (tw r) (tw k)).hom) := by
  unfold Functor.termwiseCompositeTransformation
  rw [assoc_paste]
  rw [whisker_paste]
  rw [assoc_paste]
  exact localization_paste
    (tw i) (tw p) (tw q) (tw s) (tw j) (tw b) (tw k) (tw r)
    ((Functor.whiskeringRightObjCompIso i p).hom ≫
      (Functor.whiskeringRight ℕᵒᵖ A E).map βt ≫
      (Functor.whiskeringRightObjCompIso q b).inv)
    ((Functor.whiskeringRight ℕᵒᵖ D D).map pt)
    ((Functor.whiskeringRightObjCompIso j b).inv ≫
      (Functor.whiskeringRight ℕᵒᵖ C E).map τj)
    ((Functor.whiskeringRightObjCompIso q s).inv ≫
      (Functor.whiskeringRight ℕᵒᵖ A C).map et)
    β π a e (by simpa only [Functor.termwiseCompositeTransformation] using hβ)
    hπ (by simpa only [termwiseCompHom] using ha)
    (by simpa only [termwiseCompHom] using he)

end DescentCalculus
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The recorded derived alpha is exactly the localization of the intrinsic ordinary arrow.
Source: Stacks, Tag 0F7B
(blueprint: def-cbc-strict-tower-ordinary-proper-open-arrows).
Proof: exact localization preserves the open-unit transpose and its inverse,
the direct-image unit on the clopen, and the unit-preserving adjoint compositors.
ClopenProjectorDescent expresses this equality by its equation after the localization
functor, which determines the descended natural transformation uniquely.
Consequently each factor of singleAlpha localizes to the corresponding factor in alpha;
functoriality of localization identifies their composites. -/
theorem alpha_eq_localized_singleAlpha {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    ClopenProjectorDescent (A := Towers B S) (D := Towers B W)
      (aA := clopenTowerAbelian B S) (aD := clopenTowerAbelian B W)
      (towerJ B i ⋙ towerPullback B p) (towerPullback B r ⋙ towerJ B k)
      (towerAlpha B k r p i h)
      ((@Functor.mapDerivedCategoryCompIso
        (Towers B S) inferInstance (clopenTowerAbelian B S) (towers_hasDerivedCategory B S)
        (Towers B T) inferInstance (clopenTowerAbelian B T) (towers_hasDerivedCategory B T)
        (Towers B W) inferInstance (clopenTowerAbelian B W) (towers_hasDerivedCategory B W)
        (towerJ B i) inferInstance inferInstance inferInstance
        (towerPullback B p) inferInstance inferInstance inferInstance).inv ≫ alpha B k r p i h ≫
      (@Functor.mapDerivedCategoryCompIso
        (Towers B S) inferInstance (clopenTowerAbelian B S) (towers_hasDerivedCategory B S)
        (Towers B V) inferInstance (clopenTowerAbelian B V) (towers_hasDerivedCategory B V)
        (Towers B W) inferInstance (clopenTowerAbelian B W) (towers_hasDerivedCategory B W)
        (towerPullback B r) inferInstance inferInstance inferInstance
        (towerJ B k) inferInstance inferInstance inferInstance).hom) := by
  let q := pullback.snd p i
  let b := pullback.fst p i
  let s := squareLift k r p i h
  obtain ⟨C, c, hc, hc'⟩ := (properOpen_clopen_geometry k r p i h).2.2.2.2
  let : IsOpenImmersion c := hc
  exact module_localization_paste
    (aA := ordinaryAbelian B S) (aD := ordinaryAbelian B (pullback p i))
    (aE := ordinaryAbelian B W) (aC := ordinaryAbelian B V) (aT := ordinaryAbelian B T)
    (hA := towers_hasDerivedCategory B S) (hD := towers_hasDerivedCategory B (pullback p i))
    (hE := towers_hasDerivedCategory B W) (hC := towers_hasDerivedCategory B V)
    (hT := towers_hasDerivedCategory B T)
    (moduleJ B i) (modulePullback B p) (modulePullback B q) (modulePullback B s)
    (moduleJ B s) (moduleJ B b) (moduleJ B k) (modulePullback B r)
    (openBetaModule B q b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom
    (clopenModulePi B s)
    ((openBetaModuleJComp B s b).hom ≫ (singleJCongr B (pullback.lift_fst k r h)).hom)
    ((moduleGComp B s q).inv ≫
      (eqToIso (congrArg (modulePullback B) (pullback.lift_snd k r h))).hom)
    (beta B q b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom
    (pi B s) ((jComp B s b).hom ≫ (jCongr B (pullback.lift_fst k r h)).hom)
    ((gComp B s q).inv ≫ (eqToIso (congrArg (G B) (pullback.lift_snd k r h))).hom)
    (by simpa only [Functor.termwiseCompositeTransformation, openBetaTower,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom] using
        beta_fac B q b i p pullback.condition.symm (IsPullback.of_hasPullback p i).flip)
    (pi_fac B s c hc')
    (jTail_fac B s b k (pullback.lift_fst k r h))
    (gTail_fac B s q r (pullback.lift_snd k r h))


end AlgebraicGeometry.ProEtale.StrictTower
