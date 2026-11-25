/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaRestriction
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents

/-! # Intrinsic alpha horizontal identity on module sheaves

Source: Stacks Project, Tag 0F7D, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-horizontal-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp

private theorem moduleJ_map_injective {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {N : Modules B X} {M : Modules B U}
    (f g : N ⟶ (moduleJ B j).obj M)
    (h : (modulePullback B j).map f = (modulePullback B j).map g) : f = g := by
  let A := ModuleCat.{u + 1} B
  let P := fixedRestriction B X
  let R := upperStar A j
  let e := (fixedOpen B j).app M
  have he : R.map (P.map f ≫ e.hom) = R.map (P.map g ≫ e.hom) := by
    apply (cancel_epi ((fixedPull B j).hom.app N)).1
    simp only [Functor.map_comp, ← Category.assoc]
    have hf := (fixedPull B j).hom.naturality f
    have hg := (fixedPull B j).hom.naturality g
    dsimp only [Functor.comp_map] at hf hg
    rw [← hf, ← hg]
    rw [h]
  have hm : P.map f ≫ e.hom = P.map g ≫ e.hom := by
    have := mono_openImmersionLowerShriekToLowerStar_app A j
      ((fixedRestriction B U).obj M)
    apply (cancel_mono ((openImmersionLowerShriekToLowerStar A j).app
      ((fixedRestriction B U).obj M))).1
    apply ((upperStarLowerStarAdjunction A j).homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp]
    have he' := he
    dsimp only [R] at he'
    simp only [Functor.map_comp] at he'
    rw [he']
  exact P.map_injective ((cancel_mono e.hom).1 hm)

private theorem inverse_congr {C : Type*} [Category C] {X Y : C}
    (f g : X ⟶ Y) [IsIso f] [IsIso g] (h : f = g) : inv f = inv g :=
  (Iso.inv_eq_inv (asIso f) (asIso g)).2 h

private instance unitInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (moduleOpenUnitInv B j) := by
  have := clopenModule_openUnit_isIso B j
  unfold moduleOpenUnitInv
  infer_instance

private theorem moduleOpenUnitInv_comp {U V X : Scheme.{u}}
    (j : U ⟶ V) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (M : Modules B U) :
    (modulePullback B (j ≫ k)).map ((openBetaModuleJComp B j k).hom.app M) ≫
        (moduleOpenUnitInv B (j ≫ k)).app M =
      (moduleGComp B j k).hom.app ((moduleJ B k).obj ((moduleJ B j).obj M)) ≫
        (modulePullback B j).map ((moduleOpenUnitInv B k).app ((moduleJ B j).obj M)) ≫
        (moduleOpenUnitInv B j).app M := by
  have := clopenModule_openUnit_isIso B j
  have := clopenModule_openUnit_isIso B k
  have := clopenModule_openUnit_isIso B (j ≫ k)
  have hu := unit_conjugateEquiv ((moduleJAdj B j).comp (moduleJAdj B k))
    (moduleJAdj B (j ≫ k)) (openBetaModuleJComp B j k).inv M
  rw [openBetaModuleJComp, Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  simp only [Adjunction.comp_unit_app] at hu
  have hi := inverse_congr _ _ hu
  simp only [IsIso.inv_comp] at hi
  simp only [Iso.symm_hom, ← Functor.map_inv, NatIso.inv_inv_app] at hi
  simpa only [Adjunction.comp_unit_app, IsIso.inv_comp, Functor.map_inv,
    Iso.symm_hom, NatIso.inv_inv_app, Iso.symm_inv, moduleOpenUnitInv,
    openBetaModuleJComp, NatIso.isIso_inv_app, Functor.comp_obj, Category.assoc] using hi.symm

/-- Intrinsic alpha obeys horizontal pasting on module sheaves.
Source: Stacks, Tag 0F7D, and the parent restriction argument, steps 1--3 and 5
(blueprint: lem-cbc-proper-open-alpha-horizontal-modules).
Proof: First detect equality of maps to open extension on module sheaves. Transport
to sheaves of B-modules and compose with the monomorphism from extension by zero
to direct image. The restriction/direct-image adjunction detects equality there.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For horizontal pasting, restrict along lk. The second alpha reduces q* j! i! to
p* i!; the open unit for l and then the first alpha reduce this to r*. The
unit-preserving open compositor identifies the successive open units with the
outer open unit. Detection along lk identifies the pasted and intrinsic outer maps.
Apply this calculation to every module sheaf M to obtain the displayed component
identity. Empty schemes and the zero coefficient ring give the unique zero maps;
identity opens give the unit-normalized inverse-image compositor identity. -/
theorem singleAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    ∀ M : Modules B C,
      (modulePullback B q).map ((openBetaModuleJComp B i j).hom.app M) ≫
          (singleAlpha B (k ≫ l) r q (i ≫ j) h).app M =
        (singleAlpha B l p q j h₂).app ((moduleJ B i).obj M) ≫
          (moduleJ B l).map ((singleAlpha B k r p i h₁).app M) ≫
          (openBetaModuleJComp B k l).hom.app ((modulePullback B r).obj M) := by
  intro M
  apply moduleJ_map_injective B (k ≫ l)
  apply (cancel_mono ((moduleOpenUnitInv B (k ≫ l)).app
    ((modulePullback B r).obj M))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [singleAlpha_restriction]
  have ho := (moduleSquareG B (k ≫ l) r q (i ≫ j) h).inv.naturality
    ((openBetaModuleJComp B i j).hom.app M)
  dsimp only [Functor.comp_map] at ho
  rw [reassoc_of% ho]
  rw [← (modulePullback B r).map_comp, moduleOpenUnitInv_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (moduleSquare_pasting_inv B q p r j i l k h₂ h₁ h
    ((moduleJ B j).obj ((moduleJ B i).obj M)))]
  rw [moduleOpenUnitInv_comp B k l ((modulePullback B r).obj M)]
  have hk₁ := (moduleGComp B k l).hom.naturality
    ((moduleJ B l).map ((singleAlpha B k r p i h₁).app M))
  have hk₂ := (moduleGComp B k l).hom.naturality
    ((singleAlpha B l p q j h₂).app ((moduleJ B i).obj M))
  dsimp only [Functor.comp_map] at hk₁ hk₂
  rw [reassoc_of% hk₁, reassoc_of% hk₂]
  have hn := (moduleOpenUnitInv B l).naturality ((singleAlpha B k r p i h₁).app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hn' := congrArg ((modulePullback B k).map) hn
  simp only [Functor.map_comp] at hn'
  rw [reassoc_of% hn']
  rw [← (modulePullback B k).map_comp_assoc,
    singleAlpha_restriction B l p q j h₂, (modulePullback B k).map_comp,
    Category.assoc, singleAlpha_restriction B k r p i h₁]
  have hs := (moduleSquareG B k r p i h₁).inv.naturality
    ((moduleOpenUnitInv B j).app ((moduleJ B i).obj M))
  dsimp only [Functor.comp_map, Functor.id_obj] at hs
  rw [reassoc_of% hs]

open CategoryTheory.ExactDerivedPasting

private structure NativeHorizontalData (Xa Xc Xe Xb Xd Xf : Scheme.{u}) where
  K : Modules B Xa ⥤ Modules B Xb
  L : Modules B Xb ⥤ Modules B Xe
  KL : Modules B Xa ⥤ Modules B Xe
  V : Modules B Xc ⥤ Modules B Xd
  J : Modules B Xd ⥤ Modules B Xf
  VJ : Modules B Xc ⥤ Modules B Xf
  R : Modules B Xc ⥤ Modules B Xa
  P : Modules B Xd ⥤ Modules B Xb
  Q : Modules B Xf ⥤ Modules B Xe
  a₁ : V ⋙ P ⟶ R ⋙ K
  a₂ : J ⋙ Q ⟶ P ⋙ L
  ao : VJ ⋙ Q ⟶ R ⋙ KL
  ci : V ⋙ J ⟶ VJ
  ck : K ⋙ L ⟶ KL
  h : ∀ M : Modules B Xc,
      Q.map (ci.app M) ≫ ao.app M =
        a₂.app (V.obj M) ≫ L.map (a₁.app M) ≫ ck.app (R.obj M)

@[irreducible] private def nativeHorizontalData {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    NativeHorizontalData B A C E B₀ D F where
  K := moduleJ B k
  L := moduleJ B l
  KL := moduleJ B (k ≫ l)
  V := moduleJ B i
  J := moduleJ B j
  VJ := moduleJ B (i ≫ j)
  R := modulePullback B r
  P := modulePullback B p
  Q := modulePullback B q
  a₁ := singleAlpha B k r p i h₁
  a₂ := singleAlpha B l p q j h₂
  ao := singleAlpha B (k ≫ l) r q (i ≫ j) h
  ci := (openBetaModuleJComp B i j).hom
  ck := (openBetaModuleJComp B k l).hom
  h := singleAlpha_horizontal B k l i j r p q h₁ h₂ h

private theorem nativeHorizontalLaw {A C E B₀ D F : Scheme.{u}}
    (T₀ : NativeHorizontalData B A C E B₀ D F) :
    Functor.whiskerRight (termwiseCompHom T₀.V T₀.J T₀.VJ T₀.ci) (twFunctor (fun X : Scheme.{u} ↦
      Modules B X) T₀.Q) ≫
        Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.VJ T₀.Q T₀.R T₀.KL T₀.ao =
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X :
      Scheme.{u} ↦ Modules B X) T₀.J) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.Q)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V)
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.J T₀.Q T₀.P T₀.L T₀.a₂) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.V) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.P) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.L)).inv ≫
        Functor.whiskerRight
          (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.V T₀.P T₀.R T₀.K T₀.a₁)
          (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.L) ≫
        (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.K) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.L)).hom ≫
        Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R) (termwiseCompHom
      T₀.K T₀.L T₀.KL T₀.ck) :=
  @horizontalTowerLaw Scheme.{u} (fun X : Scheme.{u} ↦ Modules B X)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Modules B X))) A C E B₀ D F
    T₀.K T₀.L T₀.KL T₀.V T₀.J T₀.VJ T₀.R T₀.P T₀.Q T₀.a₁ T₀.a₂ T₀.ao T₀.ci T₀.ck T₀.h

private theorem towerAlpha_horizontal {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    Functor.whiskerRight (termwiseCompHom (moduleJ B i) (moduleJ B j) (moduleJ B (i ≫ j))
      (openBetaModuleJComp B i j).hom) (towerPullback B q) ≫ (towerAlpha B (k ≫ l) r q (i ≫ j) h) =
      (Functor.associator (towerJ B i) (towerJ B j) (towerPullback B q)).hom ≫
      Functor.whiskerLeft (towerJ B i) (towerAlpha B l p q j h₂) ≫
        (Functor.associator (towerJ B i) (towerPullback B p) (towerJ B l)).inv ≫
      Functor.whiskerRight (towerAlpha B k r p i h₁) (towerJ B l) ≫
        (Functor.associator (towerPullback B r) (towerJ B k) (towerJ B l)).hom ≫
      Functor.whiskerLeft (towerPullback B r) (termwiseCompHom (moduleJ B k) (moduleJ B l)
      (moduleJ B (k ≫ l)) (openBetaModuleJComp B k l).hom) := by
  with_unfolding_all
    exact nativeHorizontalLaw B (nativeHorizontalData B k l i j r p q h₁ h₂ h)

-- Capture the public derived-category instances before installing the tower instance.
private abbrev nativeHorizontalDerivedFunctor (X Y : Scheme.{u}) :=
  Derived B X ⥤ Derived B Y

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

private theorem nativeHorizontalDerivedExternal {Xa Xc Xe Xb Xd Xf : Scheme.{u}}
    (K : Towers B Xa ⥤ₑ Towers B Xb)
    (L : Towers B Xb ⥤ₑ Towers B Xe)
    (KL : Towers B Xa ⥤ₑ Towers B Xe)
    (V : Towers B Xc ⥤ₑ Towers B Xd)
    (J : Towers B Xd ⥤ₑ Towers B Xf)
    (VJ : Towers B Xc ⥤ₑ Towers B Xf)
    (R : Towers B Xc ⥤ₑ Towers B Xa)
    (P : Towers B Xd ⥤ₑ Towers B Xb)
    (Q : Towers B Xf ⥤ₑ Towers B Xe)
    (KD : nativeHorizontalDerivedFunctor B Xa Xb)
    (LD : nativeHorizontalDerivedFunctor B Xb Xe)
    (KLD : nativeHorizontalDerivedFunctor B Xa Xe)
    (VD : nativeHorizontalDerivedFunctor B Xc Xd)
    (JD : nativeHorizontalDerivedFunctor B Xd Xf)
    (VJD : nativeHorizontalDerivedFunctor B Xc Xf)
    (RD : nativeHorizontalDerivedFunctor B Xc Xa)
    (PD : nativeHorizontalDerivedFunctor B Xd Xb)
    (QD : nativeHorizontalDerivedFunctor B Xf Xe)
    (hKD : K.obj.mapDerivedCategory = KD)
    (hLD : L.obj.mapDerivedCategory = LD)
    (hKLD : KL.obj.mapDerivedCategory = KLD)
    (hVD : V.obj.mapDerivedCategory = VD)
    (hJD : J.obj.mapDerivedCategory = JD)
    (hVJD : VJ.obj.mapDerivedCategory = VJD)
    (hRD : R.obj.mapDerivedCategory = RD)
    (hPD : P.obj.mapDerivedCategory = PD)
    (hQD : Q.obj.mapDerivedCategory = QD)
    (a₁ : V.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (a₂ : J.obj ⋙ Q.obj ⟶ P.obj ⋙ L.obj)
    (ao : VJ.obj ⋙ Q.obj ⟶ R.obj ⋙ KL.obj)
    (ci : V.obj ⋙ J.obj ⟶ VJ.obj)
    (ck : K.obj ⋙ L.obj ⟶ KL.obj)
    (d₁ : VD ⋙ PD ⟶
      RD ⋙ KD)
    (d₂ : JD ⋙ QD ⟶
      PD ⋙ LD)
    (d₀ : VJD ⋙ QD ⟶
      RD ⋙ KLD)
    (di : VD ⋙ JD ⟶ VJD)
    (dk : KD ⋙ LD ⟶ KLD)
    (c₁ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge P))
      (R := .comp (.edge R) (.edge K)) a₁) d₁)
    (c₂ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge J) (.edge Q))
      (R := .comp (.edge P) (.edge L)) a₂) d₂)
    (c₀ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge VJ) (.edge Q))
      (R := .comp (.edge R) (.edge KL)) ao) d₀)
    (ciFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge V) (.edge J))
      (R := .edge VJ) ci) di)
    (ckFac : HEq (Word.cell (pastingCategories B) (P := .comp (.edge K) (.edge L))
      (R := .edge KL) ck) dk)
    (law : Functor.whiskerRight ci Q.obj ≫ ao =
      (Functor.associator V.obj J.obj Q.obj).hom ≫ Functor.whiskerLeft V.obj a₂ ≫
        (Functor.associator V.obj P.obj L.obj).inv ≫ Functor.whiskerRight a₁ L.obj ≫
        (Functor.associator R.obj K.obj L.obj).hom ≫ Functor.whiskerLeft R.obj ck)
    : ∀ N : Derived B Xc,
      QD.map (di.app N) ≫ d₀.app N =
        d₂.app (VD.obj N) ≫ LD.map
      (d₁.app N) ≫
          dk.app (RD.obj N) := by
  cases hKD
  cases hLD
  cases hKLD
  cases hVD
  cases hJD
  cases hVJD
  cases hRD
  cases hPD
  cases hQD
  exact
    @genericHorizontalDerived Scheme.{u} (pastingCategories B)
      (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
      (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X)
      Xa Xc Xe Xb Xd Xf
      K L KL V J VJ R P Q a₁ a₂ ao ci ck d₁ d₂
        d₀ di dk (eq_of_heq c₁) (eq_of_heq c₂)
        (eq_of_heq c₀) (eq_of_heq ciFac) (eq_of_heq ckFac) law

private theorem horizontal_derived {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    ∀ N : Derived B C,
      (G B q).map ((jComp B i j).hom.app N) ≫
          (alpha B (k ≫ l) r q (i ≫ j) h).app N =
        (alpha B l p q j h₂).app ((J B i).obj N) ≫
          (J B l).map ((alpha B k r p i h₁).app N) ≫
          (jComp B k l).hom.app ((G B r).obj N) := by
  exact @nativeHorizontalDerivedExternal B _ A C E B₀ D F
    (ExactFunctor.of (towerJ B k))
    (ExactFunctor.of (towerJ B l))
    (ExactFunctor.of (towerJ B (k ≫ l)))
    (ExactFunctor.of (towerJ B i))
    (ExactFunctor.of (towerJ B j))
    (ExactFunctor.of (towerJ B (i ≫ j)))
    (ExactFunctor.of (towerPullback B r))
    (ExactFunctor.of (towerPullback B p))
    (ExactFunctor.of (towerPullback B q))
    (by
      with_unfolding_all
        exact J B k)
    (by
      with_unfolding_all
        exact J B l)
    (by
      with_unfolding_all
        exact J B (k ≫ l))
    (by
      with_unfolding_all
        exact J B i)
    (by
      with_unfolding_all
        exact J B j)
    (by
      with_unfolding_all
        exact J B (i ≫ j))
    (by
      with_unfolding_all
        exact G B r)
    (by
      with_unfolding_all
        exact G B p)
    (by
      with_unfolding_all
        exact G B q)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (by
      with_unfolding_all rfl)
    (towerAlpha B k r p i h₁)
    (towerAlpha B l p q j h₂)
    (towerAlpha B (k ≫ l) r q (i ≫ j) h)
    (termwiseCompHom (moduleJ B i) (moduleJ B j) (moduleJ B (i ≫ j)) (openBetaModuleJComp B i
        j).hom)
    (termwiseCompHom (moduleJ B k) (moduleJ B l) (moduleJ B (k ≫ l)) (openBetaModuleJComp B k
        l).hom)
    (by
      with_unfolding_all
        exact alpha B k r p i h₁)
    (by
      with_unfolding_all
        exact alpha B l p q j h₂)
    (by
      with_unfolding_all
        exact alpha B (k ≫ l) r q (i ≫ j) h)
    (by
      with_unfolding_all
        exact (jComp B i j).hom)
    (by
      with_unfolding_all
        exact (jComp B k l).hom)
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k r p i h₁))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B l p q j h₂))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B (k ≫ l) r q (i ≫ j) h))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingJComp B i j))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingJComp B k l))
    (by
      exact towerAlpha_horizontal B k l i j r p q h₁ h₂ h)

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
