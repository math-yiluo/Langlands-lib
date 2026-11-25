/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.ExactDerivedPastingComponents
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import WeilConjectures.AlgebraicGeometry.StrictTower.SingleAlphaRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing

/-! # Intrinsic alpha vertical identity on module sheaves

Source: Stacks Project, Tag 0F7C, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-proper-open-alpha-vertical-modules)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
  moduleSquareG fixedRestriction

private theorem open_target_detection {U X : Scheme.{u}} (k : U ⟶ X)
    [IsOpenImmersion k] {M : Modules B X} {N : Modules B U}
    (f g : M ⟶ (moduleJ B k).obj N)
    (h : (modulePullback B k).map f = (modulePullback B k).map g) : f = g := by
  let P := fixedRestriction B X
  let Q := fixedRestriction B U
  let R := upperStar (ModuleCat.{u + 1} B) k
  have : P.Faithful := fixedRestriction_faithful B X
  have hp : R.map (P.map f) = R.map (P.map g) := by
    apply (cancel_epi ((fixedPull B k).hom.app M)).1
    have hf := (fixedPull B k).hom.naturality f
    have hg := (fixedPull B k).hom.naturality g
    dsimp only [Functor.comp_map] at hf hg
    exact hf.symm.trans ((congrArg (fun t ↦ Q.map t ≫
      (fixedPull B k).hom.app _) h).trans hg)
  apply P.map_injective
  apply (cancel_mono ((fixedOpen B k).hom.app N)).1
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) k
  apply (cancel_mono (a.unit.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) k).obj (Q.obj N)))).1
  have hf := a.unit.naturality (P.map f ≫ (fixedOpen B k).hom.app N)
  have hg := a.unit.naturality (P.map g ≫ (fixedOpen B k).hom.app N)
  simp only [Functor.id_map] at hf hg
  dsimp only [Functor.comp_obj] at hf hg
  rw [hf, hg]
  simp only [Functor.comp_map, Functor.map_comp]
  change a.unit.app (P.obj M) ≫ (lowerStar (ModuleCat.{u + 1} B) k).map
      (R.map (P.map f) ≫ R.map ((fixedOpen B k).hom.app N)) = _
  rw [hp]
  simp only [R, Functor.map_comp]

/-- Intrinsic alpha obeys vertical pasting on module sheaves.
Source: Stacks, Tag 0F7C, and the parent restriction argument, steps 1--3 and 4
(blueprint: lem-cbc-proper-open-alpha-vertical-modules).
Proof: Detect equality of maps to open extension by its monomorphism into direct image.
Transport through the fixed-coefficient equivalence and use naturality of the
restriction/direct-image unit. Equality after open restriction therefore suffices.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For vertical pasting, restrict along k and use p₁k = ir₁. The second square reduces
the input to r₁* r₂* of the original module. The first alpha is then the identity
under its open-unit identification. The inverse-image compositor identifies this
with the restriction of intrinsic outer alpha. Detection gives the module equation.
Apply this calculation to every module sheaf M to obtain the displayed component
identity. Empty schemes and the zero coefficient ring give the unique zero maps;
identity opens give the unit-normalized inverse-image compositor identity. -/
theorem singleAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    ∀ M : Modules B E,
      (moduleGComp B p₁ p₂).hom.app ((moduleJ B j).obj M) ≫
          (modulePullback B p₁).map ((singleAlpha B i r₂ p₂ j h₂).app M) ≫
          (singleAlpha B k r₁ p₁ i h₁).app ((modulePullback B r₂).obj M) =
        (singleAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (moduleJ B k).map ((moduleGComp B r₁ r₂).hom.app M) := by
  intro M
  apply open_target_detection.{u} B k
  have hs := moduleSquare_pasting_inv B j i k p₂ p₁ r₂ r₁
    h₂.symm h₁.symm h.symm ((moduleJ B j).obj M)
  rw [moduleSquare_flip B i r₂ p₂ j h₂,
    moduleSquare_flip B k r₁ p₁ i h₁,
    moduleSquare_flip B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h] at hs
  simp only [Iso.symm_inv] at hs
  apply (Iso.cancel_iso_hom_left
    ((moduleSquareG B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app ((moduleJ B j).obj M)) _ _).1
  simp only [Functor.map_comp, Iso.app_hom, Functor.comp_obj]
  rw [← reassoc_of% hs]
  have hn := (moduleSquareG B k r₁ p₁ i h₁).hom.naturality
    ((singleAlpha B i r₂ p₂ j h₂).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  rw [singleAlpha_restriction_normalized B k r₁ p₁ i h₁]
  rw [← (modulePullback B r₁).map_comp_assoc]
  rw [singleAlpha_restriction_normalized B i r₂ p₂ j h₂]
  simp only [Functor.map_comp, Category.assoc]
  have hi_iso := clopenModule_openUnit_isIso B i
  have hi := (asIso (moduleJAdj B i).unit).hom_inv_id_app
    ((modulePullback B r₂).obj M)
  have hi' : (modulePullback B r₁).map
      ((moduleJAdj B i).unit.app ((modulePullback B r₂).obj M)) ≫
      (modulePullback B r₁).map ((asIso (moduleJAdj B i).unit).inv.app
        ((modulePullback B r₂).obj M)) = 𝟙 _ := by
    rw [← (modulePullback B r₁).map_comp]
    simpa only [asIso_hom, CategoryTheory.Functor.map_id] using
      congrArg (modulePullback B r₁).map hi
  rw [reassoc_of% hi']
  have hc := (moduleGComp B r₁ r₂).hom.naturality
    ((@asIso _ _ _ _ (moduleJAdj B j).unit
      (clopenModule_openUnit_isIso B j)).inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc
  rw [← reassoc_of% hc]
  rw [reassoc_of% singleAlpha_restriction_normalized B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h M]
  have hu := (moduleJAdj B k).unit.naturality ((moduleGComp B r₁ r₂).hom.app M)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hu
  rw [hu]

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false

private structure NativeVerticalData (A C E B₀ D F : Scheme.{u}) where
  K : Modules B A ⥤ Modules B B₀
  L : Modules B C ⥤ Modules B D
  J : Modules B E ⥤ Modules B F
  R₁ : Modules B C ⥤ Modules B A
  R₂ : Modules B E ⥤ Modules B C
  R : Modules B E ⥤ Modules B A
  P₁ : Modules B D ⥤ Modules B B₀
  P₂ : Modules B F ⥤ Modules B D
  P : Modules B F ⥤ Modules B B₀
  a₁ : L ⋙ P₁ ⟶ R₁ ⋙ K
  a₂ : J ⋙ P₂ ⟶ R₂ ⋙ L
  ao : J ⋙ P ⟶ R ⋙ K
  cp : P ≅ P₂ ⋙ P₁
  cr : R ≅ R₂ ⋙ R₁
  h : ∀ M : Modules B E,
    cp.hom.app (J.obj M) ≫ P₁.map (a₂.app M) ≫ a₁.app (R₂.obj M) =
      ao.app M ≫ K.map (cr.hom.app M)

@[irreducible] private def nativeVerticalData {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    NativeVerticalData B A C E B₀ D F where
  K := moduleJ B k
  L := moduleJ B i
  J := moduleJ B j
  R₁ := modulePullback B r₁
  R₂ := modulePullback B r₂
  R := modulePullback B (r₁ ≫ r₂)
  P₁ := modulePullback B p₁
  P₂ := modulePullback B p₂
  P := modulePullback B (p₁ ≫ p₂)
  a₁ := singleAlpha B k r₁ p₁ i h₁
  a₂ := singleAlpha B i r₂ p₂ j h₂
  ao := singleAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h
  cp := moduleGComp B p₁ p₂
  cr := moduleGComp B r₁ r₂
  h := singleAlpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h

private theorem nativeVerticalLaw {A C E B₀ D F : Scheme.{u}}
    (T₀ : NativeVerticalData B A C E B₀ D F) :
    Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.J)
        (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso T₀.cp ≪≫
          Functor.whiskeringRightObjCompIso T₀.P₂ T₀.P₁).hom) ≫
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.J) (twFunctor (fun X :
      Scheme.{u} ↦ Modules B X) T₀.P₂) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁)).inv ≫
      Functor.whiskerRight
        (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.J T₀.P₂ T₀.R₂ T₀.L T₀.a₂)
        (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁) ≫
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R₂) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.L) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.P₁)).hom ≫
      Functor.whiskerLeft (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R₂)
        (Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.L T₀.P₁ T₀.R₁ T₀.K T₀.a₁) ≫
      (Functor.associator (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.R₂) (twFunctor (fun X
      : Scheme.{u} ↦ Modules B X) T₀.R₁) (twFunctor (fun X : Scheme.{u} ↦ Modules B X) T₀.K)).inv =
    Functor.termwiseCompositeTransformation ℕᵒᵖ _ _ _ _ T₀.J T₀.P T₀.R T₀.K T₀.ao ≫
      Functor.whiskerRight
        (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso T₀.cr ≪≫
          Functor.whiskeringRightObjCompIso T₀.R₂ T₀.R₁).hom) (twFunctor (fun X : Scheme.{u} ↦
      Modules B X) T₀.K) :=
  @verticalTowerLaw Scheme.{u} (fun X : Scheme.{u} ↦ Modules B X)
    (fun X ↦ inferInstanceAs (Category.{u + 1} (Modules B X))) A C E B₀ D F
    T₀.K T₀.L T₀.J T₀.R₁ T₀.R₂ T₀.R T₀.P₁ T₀.P₂ T₀.P T₀.a₁ T₀.a₂ T₀.ao T₀.cp T₀.cr T₀.h

private theorem towerAlpha_vertical {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    Functor.whiskerLeft (towerJ B j) (towerGComp B p₁ p₂).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (towerAlpha B i r₂ p₂ j h₂) (towerPullback B p₁) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (towerPullback B r₂) (towerAlpha B k r₁ p₁ i h₁) ≫
        (Functor.associator _ _ _).inv =
      towerAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h ≫
        Functor.whiskerRight (towerGComp B r₁ r₂).hom (towerJ B k) := by
  with_unfolding_all
    exact nativeVerticalLaw B (nativeVerticalData B k i j r₁ r₂ p₁ p₂ h₁ h₂ h)

-- Capture the public derived-category instances before installing the tower instance.
private abbrev nativeVerticalDerivedFunctor (X Y : Scheme.{u}) :=
  Derived B X ⥤ Derived B Y

section DerivedTransport
attribute [local instance] exactPairAdditive
attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local irreducible] G J alpha beta gComp jComp squareG

private theorem nativeVerticalDerivedExternal {Xa Xc Xe Xb Xd Xf : Scheme.{u}}
    (K : Towers B Xa ⥤ₑ Towers B Xb)
    (L : Towers B Xc ⥤ₑ Towers B Xd)
    (J : Towers B Xe ⥤ₑ Towers B Xf)
    (R₁ : Towers B Xc ⥤ₑ Towers B Xa)
    (R₂ : Towers B Xe ⥤ₑ Towers B Xc)
    (R : Towers B Xe ⥤ₑ Towers B Xa)
    (P₁ : Towers B Xd ⥤ₑ Towers B Xb)
    (P₂ : Towers B Xf ⥤ₑ Towers B Xd)
    (P : Towers B Xf ⥤ₑ Towers B Xb)
    (KD : nativeVerticalDerivedFunctor B Xa Xb)
    (LD : nativeVerticalDerivedFunctor B Xc Xd)
    (JD : nativeVerticalDerivedFunctor B Xe Xf)
    (R₁D : nativeVerticalDerivedFunctor B Xc Xa)
    (R₂D : nativeVerticalDerivedFunctor B Xe Xc)
    (RD : nativeVerticalDerivedFunctor B Xe Xa)
    (P₁D : nativeVerticalDerivedFunctor B Xd Xb)
    (P₂D : nativeVerticalDerivedFunctor B Xf Xd)
    (PD : nativeVerticalDerivedFunctor B Xf Xb)
    (hKD : K.obj.mapDerivedCategory = KD)
    (hLD : L.obj.mapDerivedCategory = LD)
    (hJD : J.obj.mapDerivedCategory = JD)
    (hR₁D : R₁.obj.mapDerivedCategory = R₁D)
    (hR₂D : R₂.obj.mapDerivedCategory = R₂D)
    (hRD : R.obj.mapDerivedCategory = RD)
    (hP₁D : P₁.obj.mapDerivedCategory = P₁D)
    (hP₂D : P₂.obj.mapDerivedCategory = P₂D)
    (hPD : P.obj.mapDerivedCategory = PD)
    (a₁ : L.obj ⋙ P₁.obj ⟶ R₁.obj ⋙ K.obj)
    (a₂ : J.obj ⋙ P₂.obj ⟶ R₂.obj ⋙ L.obj)
    (ao : J.obj ⋙ P.obj ⟶ R.obj ⋙ K.obj)
    (cp : P.obj ⟶ P₂.obj ⋙ P₁.obj)
    (cr : R.obj ⟶ R₂.obj ⋙ R₁.obj)
    (d₁ : LD ⋙ P₁D ⟶
      R₁D ⋙ KD)
    (d₂ : JD ⋙ P₂D ⟶
      R₂D ⋙ LD)
    (d₀ : JD ⋙ PD ⟶
      RD ⋙ KD)
    (dp : PD ⟶ P₂D ⋙ P₁D)
    (dr : RD ⟶ R₂D ⋙ R₁D)
    (c₁ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge L) (.edge P₁))
      (R := .comp (.edge R₁) (.edge K)) a₁) d₁)
    (c₂ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge J) (.edge P₂))
      (R := .comp (.edge R₂) (.edge L)) a₂) d₂)
    (c₀ : HEq (Word.cell (pastingCategories B) (P := .comp (.edge J) (.edge P))
      (R := .comp (.edge R) (.edge K)) ao) d₀)
    (cpFac : HEq (Word.cell (pastingCategories B) (P := .edge P)
      (R := .comp (.edge P₂) (.edge P₁)) cp) dp)
    (crFac : HEq (Word.cell (pastingCategories B) (P := .edge R)
      (R := .comp (.edge R₂) (.edge R₁)) cr) dr)
    (law : Functor.whiskerLeft J.obj cp ≫ (Functor.associator J.obj P₂.obj P₁.obj).inv ≫
        Functor.whiskerRight a₂ P₁.obj ≫ (Functor.associator R₂.obj L.obj P₁.obj).hom ≫
        Functor.whiskerLeft R₂.obj a₁ ≫ (Functor.associator R₂.obj R₁.obj K.obj).inv =
      ao ≫ Functor.whiskerRight cr K.obj)
    : ∀ N : Derived B Xe,
      dp.app (JD.obj N) ≫ P₁D.map (d₂.app
      N) ≫
          d₁.app (R₂D.obj N) =
        d₀.app N ≫ KD.map (dr.app N) := by
  cases hKD
  cases hLD
  cases hJD
  cases hR₁D
  cases hR₂D
  cases hRD
  cases hP₁D
  cases hP₂D
  cases hPD
  exact
    @genericVerticalDerived Scheme.{u} (pastingCategories B)
      (fun X ↦ inferInstanceAs (Category.{u + 1} (Towers B X)))
      (fun X ↦ clopenTowerAbelian B X) (fun X ↦ towers_hasDerivedCategory B X)
      Xa Xc Xe Xb Xd Xf
      K L J R₁ R₂ R P₁ P₂ P a₁ a₂ ao cp cr d₁ d₂
        d₀ dp dr (eq_of_heq c₁) (eq_of_heq c₂)
        (eq_of_heq c₀) (eq_of_heq cpFac) (eq_of_heq crFac) law

private theorem vertical_derived {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    ∀ N : Derived B E,
      (gComp B p₁ p₂).hom.app ((J B j).obj N) ≫
          (G B p₁).map ((alpha B i r₂ p₂ j h₂).app N) ≫
          (alpha B k r₁ p₁ i h₁).app ((G B r₂).obj N) =
        (alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
          (J B k).map ((gComp B r₁ r₂).hom.app N) := by
  exact @nativeVerticalDerivedExternal B _ A C E B₀ D F
    (ExactFunctor.of (towerJ B k))
    (ExactFunctor.of (towerJ B i))
    (ExactFunctor.of (towerJ B j))
    (ExactFunctor.of (towerPullback B r₁))
    (ExactFunctor.of (towerPullback B r₂))
    (ExactFunctor.of (towerPullback B (r₁ ≫ r₂)))
    (ExactFunctor.of (towerPullback B p₁))
    (ExactFunctor.of (towerPullback B p₂))
    (ExactFunctor.of (towerPullback B (p₁ ≫ p₂)))
    (by
      with_unfolding_all
        exact J B k)
    (by
      with_unfolding_all
        exact J B i)
    (by
      with_unfolding_all
        exact J B j)
    (by
      with_unfolding_all
        exact G B r₁)
    (by
      with_unfolding_all
        exact G B r₂)
    (by
      with_unfolding_all
        exact G B (r₁ ≫ r₂))
    (by
      with_unfolding_all
        exact G B p₁)
    (by
      with_unfolding_all
        exact G B p₂)
    (by
      with_unfolding_all
        exact G B (p₁ ≫ p₂))
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
    (towerAlpha B k r₁ p₁ i h₁)
    (towerAlpha B i r₂ p₂ j h₂)
    (towerAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    ((towerGComp B p₁ p₂).hom)
    ((towerGComp B r₁ r₂).hom)
    (by
      with_unfolding_all
        exact alpha B k r₁ p₁ i h₁)
    (by
      with_unfolding_all
        exact alpha B i r₂ p₂ j h₂)
    (by
      with_unfolding_all
        exact alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
    (by
      with_unfolding_all
        exact (gComp B p₁ p₂).hom)
    (by
      with_unfolding_all
        exact (gComp B r₁ r₂).hom)
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k r₁ p₁ i h₁))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B i r₂ p₂ j h₂))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingGComp B p₁ p₂))
    (by
      with_unfolding_all
        exact heq_of_eq (pastingGComp B r₁ r₂))
    (by
      exact towerAlpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h)

end DerivedTransport

end AlgebraicGeometry.ProEtale.StrictTower
