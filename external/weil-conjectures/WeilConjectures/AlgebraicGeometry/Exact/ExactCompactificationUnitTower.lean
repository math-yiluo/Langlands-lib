/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Exact.ExactCompactificationUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.Open.OpenExchangeDerivedUnit
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedDerivedUnitPasting
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate

/-!
# The exact derived unit on one compatible compactification tower

Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-tower).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private lemma proper_comp_eq
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Functor.rightDerivedFunctorCompIso'
      (lowerStar (ModuleCat.{u + 1} A) f) (lowerStar (ModuleCat.{u + 1} A) g)
      (lowerStarComp (ModuleCat.{u + 1} A) f g)).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom := by
  let B := ModuleCat.{u + 1} A
  have hh := Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction B f) (upperStarLowerStarAdjunction B g)
    (upperStarLowerStarAdjunction B (f ≫ g)) (lowerStarComp B f g)
    (upperStarComp B f g) (by
      exact (congrArg Iso.hom (conjugateIsoEquiv_upperStarComp B f g)).symm)
  simpa [rightDerivedLowerStarComp, conjugateIsoEquiv,
    mapDerivedUpperStarLowerStarAdjunction] using hh

private noncomputable abbrev nunit
    {C₀ D₀ E₀ : Type*} [Category C₀] [Category D₀] [Category E₀]
    [Abelian C₀] [Abelian D₀] [Abelian E₀]
    [HasDerivedCategory C₀] [HasDerivedCategory D₀] [HasDerivedCategory E₀]
    [Abelian.HasKInjectiveResolutions D₀]
    (F₀ : C₀ ⥤ E₀) (J₀ : C₀ ⥤ D₀) (R₀ : D₀ ⥤ E₀)
    [F₀.Additive] [J₀.Additive] [R₀.Additive]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits J₀] [PreservesFiniteColimits J₀]
    (a₀ : F₀ ⟶ J₀ ⋙ R₀) :=
  normalizationLocalizationDesc DerivedCategory.Qh (HomotopyCategory.quasiIso C₀ (.up ℤ))
    (normalizationHomotopyTransformation F₀ J₀ R₀ a₀)

private theorem open_compare_comp (A : Type (u + 1)) [CommRing A]
    {U V W : Scheme.{u}} (k : U ⟶ V) (i : V ⟶ W)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (k ≫ i)).app F =
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) k i).hom.app F ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((k)_!open[ModuleCat.{u + 1} A].obj F) ≫
        (i)_*[ModuleCat.{u + 1} A].map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) k i).hom.app F := by
  apply openImmersionLowerShriek_lowerStar_hom_ext
  rw [unit_map_openImmersionLowerShriekToLowerStar_app_counit]
  symm
  simp only [Functor.map_comp, Category.assoc]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (k ≫ i))
    (((openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k).comp
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)).ofNatIsoRight
        (upperStarComp (ModuleCat.{u + 1} A) k i).symm) F
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Adjunction.comp_unit_app,
    Functor.comp_obj] at hu
  erw [← Category.assoc, hu]
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc]
  rw [← NatTrans.naturality_assoc, ← NatTrans.naturality_assoc]
  erw [upperStarComp_inv_app_counit_app (ModuleCat.{u + 1} A) k i F]
  simp only [Functor.comp_map]
  have hh := (lowerStarComp (ModuleCat.{u + 1} A) k i).hom_inv_id_app F
  have hhh := congrArg (fun f =>
    (k)^*[ModuleCat.{u + 1} A].map ((i)^*[ModuleCat.{u + 1} A].map f)) hh
  simp only [Functor.map_comp, CategoryTheory.Functor.map_id] at hhh
  rw [reassoc_of% hhh]
  have hn := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).counit.naturality
    ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app F)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hkn := congrArg (fun f => (k)^*[ModuleCat.{u + 1} A].map f) hn
  simp only [Functor.map_comp] at hkn
  rw [reassoc_of% hkn]
  have hz := congrArg (fun f => (k)^*[ModuleCat.{u + 1} A].map f)
    (unit_map_openImmersionLowerShriekToLowerStar_app_counit
      (ModuleCat.{u + 1} A) i ((k)_!open[ModuleCat.{u + 1} A].obj F))
  simp only [Functor.map_comp] at hz
  erw [reassoc_of% hz, (k)^*[ModuleCat.{u + 1} A].map_id, Category.id_comp,
    unit_map_openImmersionLowerShriekToLowerStar_app_counit]

private noncomputable def open_congr
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    {j k : U ⟶ V} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) j ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} A) k := by
  subst h
  exact Iso.refl _

private lemma open_congr_derived
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    {j k : U ⟶ V} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    Functor.mapDerivedCategoryNatIso (open_congr A h) =
      mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h := by
  subst h
  apply Iso.ext
  simpa only [open_congr, mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_hom] using
    (Functor.mapDerivedCategoryNatIso_refl (F :=
      openImmersionLowerShriek (ModuleCat.{u + 1} A) j))

private lemma derived_open_congr_symm
    (A : Type (u + 1)) [CommRing A] {U V : Scheme.{u}}
    {j k : U ⟶ V} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h.symm =
      (mapDerivedCategoryOpenImmersionLowerShriekCongr (ModuleCat.{u + 1} A) h).symm := by
  subst k
  rfl

private lemma open_compare_triangle
    (A : Type (u + 1)) [CommRing A] {U V W : Scheme.{u}}
    (j : U ⟶ V) (b : V ⟶ W) (k : U ⟶ W)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion k]
    (hk : j ≫ b = k) (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((open_congr A hk.symm ≪≫
      openImmersionLowerShriekComp (ModuleCat.{u + 1} A) j b).inv.app M) ≫
        (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) k).app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) b).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) b).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) j).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) j b k hk.symm).hom.app M := by
  subst k
  simp only [open_congr, Iso.refl_trans]
  rw [open_compare_comp, Iso.inv_hom_id_app_assoc]

private lemma sheaf_exchange_inclusion
    (A : Type (u + 1)) [CommRing A]
    {U V W Z : Scheme.{u}} (b : U ⟶ V) (q : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion b] [IsOpenImmersion i] (sq : IsPullback q b i p)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _
        (@asIso _ _ _ _ _
          (isIso_openImmersionLowerShriekBaseChangeMap
            (ModuleCat.{u + 1} A) sq)).inv)).app M ≫
        (lowerStar (ModuleCat.{u + 1} A) p).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) b).app M) =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) i).app
          ((lowerStar (ModuleCat.{u + 1} A) q).obj M) ≫
        (squareLowerStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom.app M := by
  let B := ModuleCat.{u + 1} A
  let bc := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap B sq)
  have hn (N : Sheaf W.smallEtaleTopology B) :
      bc.inv.app N ≫ (openImmersionLowerShriekToLowerStar B b).app
          ((upperStar B q).obj N) =
        (upperStar B p).map ((openImmersionLowerShriekToLowerStar B i).app N) ≫
          (baseChangeMap B sq.toCommSq).app N := by
    apply (cancel_epi (bc.hom.app N)).1
    rw [Iso.hom_inv_id_app_assoc]
    exact (openImmersionLowerShriekBaseChangeMap_comp_baseChangeMap_app B
      sq.toCommSq N).symm
  have hm := congr_app (mateEquiv_baseChangeSquare B sq.toCommSq) M
  have hs := (openImmersionLowerShriekToLowerStar B b).naturality
    ((upperStarLowerStarAdjunction B q).counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hs
  have hx : (mateEquiv (upperStarLowerStarAdjunction B q)
      (upperStarLowerStarAdjunction B p)
      (TwoSquare.mk _ _ _ _ bc.inv)).app M =
      (upperStarLowerStarAdjunction B p).unit.app _ ≫
        (lowerStar B p).map (bc.inv.app _ ≫ (openImmersionLowerShriek B b).map
          ((upperStarLowerStarAdjunction B q).counit.app M)) := by
    simp [mateEquiv_apply]
  change _ ≫ _ = _
  rw [hx, Category.assoc, ← (lowerStar B p).map_comp, Category.assoc]
  erw [hs]
  rw [
    ← Category.assoc, hn, (lowerStar B p).map_comp, (lowerStar B p).map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% (upperStarLowerStarAdjunction B p).unit.naturality
    ((openImmersionLowerShriekToLowerStar B i).app ((lowerStar B q).obj M))]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map]
  simpa [baseChangeMap, baseChangeSquare, mateEquiv_apply, Functor.map_comp,
    Category.assoc] using
    congrArg (fun t ↦ (openImmersionLowerShriekToLowerStar B i).app
      ((lowerStar B q).obj M) ≫ t) hm

attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  lowerStarComp openImmersionLowerShriekComp

private lemma canonical_sheaf_tower
    (A : Type (u + 1)) [CommRing A]
    {V T B : Scheme.{u}} (h : V ⟶ T) (e : T ⟶ B)
    (d : Compactification e) (c : Compactification (h ≫ d.i))
    (χ : lowerStar (ModuleCat.{u + 1} A) c.restrict.g ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hχ : ∀ M, χ.app M ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (pullback.fst c.g d.i)).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) c.g
        (c.restrict.g ≫ d.i) c.isPullback_restrict.w).hom.app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app
          ((lowerStar (ModuleCat.{u + 1} A) c.restrict.g).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) c.restrict.g d.i).hom.app M)
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStar (ModuleCat.{u + 1} A) d.g).map
        (χ.app ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i).obj M)) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) c.g d.g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g d.i)).obj
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i).obj M)) ≫
      (lowerStar (ModuleCat.{u + 1} A) (c.g ≫ d.g)).map
        ((open_congr A c.restrict_i_fst.symm ≪≫
          openImmersionLowerShriekComp (ModuleCat.{u + 1} A) c.restrict.i
            (pullback.fst c.g d.i)).inv.app M) ≫
      (compactificationSheafToDirectImage A (d.comp c)).app M =
      (compactificationSheafToDirectImage A d).app
          ((lowerStar (ModuleCat.{u + 1} A) c.restrict.g).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i).obj M)) ≫
        (lowerStar (ModuleCat.{u + 1} A) e).map
          ((compactificationSheafToDirectImage A c.restrict).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M := by
  let K := ModuleCat.{u + 1} A
  let j := c.restrict.i
  let b := pullback.fst c.g d.i
  let q := c.restrict.g
  let p := c.g
  let i := d.i
  let s := d.g
  let k := c.i
  have ht := open_compare_triangle A j b k c.restrict_i_fst M
  have hkp := congr_app (lowerStarComp_assoc' K k p s (h ≫ i) (p ≫ s) (h ≫ e)
    c.comm rfl (by simpa only [Category.assoc] using congrArg (fun t ↦ h ≫ t) d.comm)) M
  have hjbp := congr_app (lowerStarComp_assoc' K j b p k (q ≫ i) (h ≫ i)
    c.restrict_i_fst.symm c.isPullback_restrict.w c.comm) M
  have hjqi := congr_app (lowerStarComp_assoc' K j q i h (q ≫ i) (h ≫ i)
    c.restrict.comm rfl rfl) M
  have hhis := congr_app (lowerStarComp_assoc' K h i s (h ≫ i) e (h ≫ e)
    rfl d.comm (by simpa only [Category.assoc] using congrArg (fun t ↦ h ≫ t) d.comm)) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hkp hjbp hjqi hhis
  simp only [compactificationSheafToDirectImage, NatTrans.comp_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [← (lowerStar K (p ≫ s)).map_comp_assoc, ht]
  have nv := (lowerStarComp K p s).hom.naturality
    ((openImmersionLowerShriekToLowerStar K b).app
        ((openImmersionLowerShriek K j).obj M) ≫
      (lowerStar K b).map ((openImmersionLowerShriekToLowerStar K j).app M) ≫
      (lowerStarComp K j b k c.restrict_i_fst.symm).hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nv
  erw [← reassoc_of% nv, ← hkp]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← (lowerStar K s).map_comp_assoc]
  erw [hjbp]
  have nbp := (lowerStarComp K b p (q ≫ i) c.isPullback_restrict.w).hom.naturality
    ((openImmersionLowerShriekToLowerStar K j).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nbp
  erw [reassoc_of% nbp]
  erw [← (lowerStar K s).map_comp_assoc]
  erw [reassoc_of% hχ ((openImmersionLowerShriek K j).obj M)]
  have nqi := (lowerStarComp K q i).hom.naturality
    ((openImmersionLowerShriekToLowerStar K j).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nqi
  erw [← reassoc_of% nqi, ← hjqi]
  rw [← (lowerStar K i).map_comp_assoc]
  rw [(lowerStar K s).map_comp, (lowerStar K s).map_comp]
  simp only [Category.assoc]
  rw [hhis]
  have nis := (lowerStarComp K i s e d.comm).hom.naturality
    ((compactificationSheafToDirectImage A c.restrict).app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at nis
  erw [reassoc_of% nis]
  simp only [compactificationSheafToDirectImage, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rfl

private lemma open_comparison_mono (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B]
    {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology B) :
    Mono ((openImmersionLowerShriekToLowerStar B j).app M) := by
  let γ : (openImmersionLowerShriek B j).obj M ⟶ (lowerStar B j).obj M :=
    (openImmersionLowerShriekToLowerStar B j).app M
  have hj : IsIso ((upperStar B j).map γ) :=
    (NatIso.isIso_map_iff (upperStarIsoOpenImmersionRestriction B j) γ).2 inferInstance
  have hz := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range B j
    j.closedComplement (by rw [j.range_closedComplement]; exact disjoint_compl_right) M
  have hc : Mono ((upperStar B j.closedComplement).map γ) := hz.mono _
  have hker {Y : Scheme.{u}}
      (q : Sheaf Z.smallEtaleTopology B ⥤ Sheaf Y.smallEtaleTopology B)
      [PreservesFiniteLimits q] [Mono (q.map γ)] : IsZero (q.obj (kernel γ)) :=
    (isZero_kernel_of_mono (q.map γ)).of_iso (PreservesKernel.iso q γ)
  have h0 : IsZero (kernel γ) :=
    isZero_of_isZero_upperStar (A := B) (j := j) j.closedComplement j.range_closedComplement
      (hker (upperStar B j)) (hker (upperStar B j.closedComplement))
  exact Preadditive.mono_of_isZero_kernel γ h0

private lemma compactification_comparison_mono_aux
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology B) :
    Mono ((lowerStar B c.g).map ((openImmersionLowerShriekToLowerStar B c.i).app M) ≫
      (lowerStarComp B c.i c.g f c.comm).hom.app M) := by
  have := open_comparison_mono B c.i M
  infer_instance

private lemma compactification_comparison_mono (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((compactificationSheafToDirectImage A c).app M) :=
  compactification_comparison_mono_aux (ModuleCat.{u + 1} A) c M

private lemma exactUnit_eq_nunit
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g) :
    exactCompactificationUnit A c F a = nunit F
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) a.hom := by
  unfold exactCompactificationUnit
  rfl

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  Functor.mapDerivedCategoryNatIso

private lemma normalized_sheaf_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}} [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (d : Compactification e) (c : Compactification (h ≫ d.i))
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ah : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.restrict.g)
    (ae : G ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (a : F ⋙ G ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) (d.comp c).i ⋙
      lowerStar (ModuleCat.{u + 1} A) (d.comp c).g)
    (na : ∀ M, a.hom.app M ≫ (compactificationSheafToDirectImage A (d.comp c)).app M =
      ae.hom.app (F.obj M) ≫ (compactificationSheafToDirectImage A d).app (F.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) e).map
          (ah.hom.app M ≫ (compactificationSheafToDirectImage A c.restrict).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M)
    (χ : lowerStar (ModuleCat.{u + 1} A) c.restrict.g ⋙
      openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (hχ : ∀ M, χ.app M ≫
      (lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A)
          (pullback.fst c.g d.i)).app M) ≫
      (lowerStarComp (ModuleCat.{u + 1} A) (pullback.fst c.g d.i) c.g
        (c.restrict.g ≫ d.i) c.isPullback_restrict.w).hom.app M =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) d.i).app
          ((lowerStar (ModuleCat.{u + 1} A) c.restrict.g).obj M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) c.restrict.g d.i).hom.app M)
    :
    let K := ModuleCat.{u + 1} A;
    let J := openImmersionLowerShriek K c.restrict.i;
    let R := lowerStar K c.restrict.g;
    let O := openImmersionLowerShriek K (U := c.restrict.Z) (pullback.fst c.g d.i);
    let P := lowerStar K c.g;
    let S := lowerStar K d.g;
    let H := openImmersionLowerShriek K c.i;
    let W := lowerStar K (c.g ≫ d.g);
    let eo : H ≅ J ⋙ O := open_congr A c.restrict_i_fst.symm ≪≫
      openImmersionLowerShriekComp K c.restrict.i (pullback.fst c.g d.i);
    let ep : P ⋙ S ≅ W := lowerStarComp K c.g d.g;
    let t : F ⋙ G ⟶ H ⋙ W :=
      Functor.whiskerRight ah.hom G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae.hom) ≫
        Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
        Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W;
    t = a.hom := by
  intro K J R O P S H W eo ep t
  apply NatTrans.ext
  funext M
  have := compactification_comparison_mono A (d.comp c) M
  apply (cancel_mono ((compactificationSheafToDirectImage A (d.comp c)).app M)).1
  rw [na]
  dsimp only [t, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  refine (congrArg (fun z ↦ G.map (ah.hom.app M) ≫
    ae.hom.app (R.obj (J.obj M)) ≫ z)
    (canonical_sheaf_tower A h e d c χ hχ M)).trans ?_
  have he := ae.hom.naturality (ah.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at he
  rw [reassoc_of% he]
  have hi := (compactificationSheafToDirectImage A d).naturality (ah.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hi
  rw [reassoc_of% hi, ← (lowerStar K e).map_comp_assoc]

private lemma canonical_derived_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}} [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (d : Compactification e) (c : Compactification (h ≫ d.i)) :
    let K := ModuleCat.{u + 1} A;
    let J := openImmersionLowerShriek K c.restrict.i;
    let O := openImmersionLowerShriek K (U := c.restrict.Z) (pullback.fst c.g d.i);
    let P := lowerStar K c.g;
    let S := lowerStar K d.g;
    let H := openImmersionLowerShriek K c.i;
    let W := lowerStar K (c.g ≫ d.g);
    let Γ := openImmersionLowerShriekLowerStarExchange K c.isPullback_restrict;
    let eo : H ≅ J ⋙ O := open_congr A c.restrict_i_fst.symm ≪≫
      openImmersionLowerShriekComp K c.restrict.i (pullback.fst c.g d.i);
    let ep : P ⋙ S ≅ W := lowerStarComp K c.g d.g;
    (rightDerivedLowerShriekOfCompactificationCompIso A d c).hom =
      Functor.whiskerLeft J.mapDerivedCategory (Functor.whiskerRight Γ S.rightDerivedFunctor) ≫
      Functor.whiskerLeft (J.mapDerivedCategory ⋙ O.mapDerivedCategory)
        (Functor.rightDerivedFunctorCompIso' P S ep).hom ≫
      Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eo).inv
        W.rightDerivedFunctor := by
  intro K J O P S H W Γ eo ep
  have heo : Functor.mapDerivedCategoryTriangleIso eo =
      mapDerivedCategoryOpenImmersionLowerShriekCongr K c.restrict_i_fst.symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekComp K c.restrict.i
          (pullback.fst c.g d.i) := by
    apply Iso.ext
    simp only [eo, Functor.mapDerivedCategoryTriangleIso,
      Functor.mapDerivedCategoryNatIso_trans, Iso.trans_hom, Category.assoc]
    rw [open_congr_derived]
    rfl
  rw [heo, derived_open_congr_symm A c.restrict_i_fst]
  rw [proper_comp_eq]
  ext L
  simp only [rightDerivedLowerShriekOfCompactificationCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp,
    Category.assoc, asIso_hom]
  rfl

/-- The forward unit equation on a single compatible proper/open tower. No invertibility
of the units, family of compactifications, or chosen-compactification comparison is required.
Source: Stacks Project, Tags 0F7B, 0F7J and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-tower).

Proof: take the ordinary mate of inverse open base change, and normalize it by its
composite with the support inclusion. Open composition and ordinary direct-image
associativity show that the resulting sheaf tower map has the normalization in the
hypothesis; monicity of the compactification inclusion identifies it with a. The mixed
derived mate respects the right-derived units by their adjunction factorization formulas.
Paste that identity with direct-image composition and the exact-derived triangle for the
open immersions. After precomposition with the fully faithful homotopy localization,
naturality reduces the equality to the ordinary sheaf tower map. The generic categorical
calculations are proved in the two supporting modules. No resolutions are chosen here. -/
theorem exactCompactificationUnit_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T B : Scheme.{u}} [IsNoetherian V] [IsNoetherian T] [IsNoetherian B]
    (h : V ⟶ T) (e : T ⟶ B)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (d : Compactification e) (c : Compactification (h ≫ d.i))
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (ah : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.restrict.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.restrict.g)
    (ae : G ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (a : F ⋙ G ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) (d.comp c).i ⋙
      lowerStar (ModuleCat.{u + 1} A) (d.comp c).g)
    (na : ∀ M, a.hom.app M ≫ (compactificationSheafToDirectImage A (d.comp c)).app M =
      ae.hom.app (F.obj M) ≫ (compactificationSheafToDirectImage A d).app (F.obj M) ≫
        (lowerStar (ModuleCat.{u + 1} A) e).map
          (ah.hom.app M ≫ (compactificationSheafToDirectImage A c.restrict).app M) ≫
        (lowerStarComp (ModuleCat.{u + 1} A) h e).hom.app M) :
    Functor.whiskerRight (exactCompactificationUnit A c.restrict F ah) G.mapDerivedCategory ≫
      Functor.whiskerLeft
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c.restrict)
        (exactCompactificationUnit A d G ae) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A d c).hom =
    (Functor.mapDerivedCategoryCompIso F G).hom ≫
      exactCompactificationUnit A (d.comp c) (F ⋙ G) a := by
  let K := ModuleCat.{u + 1} A
  let J := openImmersionLowerShriek K c.restrict.i
  let R := lowerStar K c.restrict.g
  let I := openImmersionLowerShriek K d.i
  let O := openImmersionLowerShriek K (U := c.restrict.Z) (pullback.fst c.g d.i)
  let P := lowerStar K c.g
  let S := lowerStar K d.g
  let H := openImmersionLowerShriek K c.i
  let W := lowerStar K (c.g ≫ d.g)
  let bc := @asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap K
    c.isPullback_restrict)
  let χ := (mateEquiv (upperStarLowerStarAdjunction K c.restrict.g)
    (upperStarLowerStarAdjunction K c.g) (TwoSquare.mk _ _ _ _ bc.inv))
  let Γ := openImmersionLowerShriekLowerStarExchange K c.isPullback_restrict
  let eo : H ≅ J ⋙ O := open_congr A c.restrict_i_fst.symm ≪≫
    openImmersionLowerShriekComp K c.restrict.i (pullback.fst c.g d.i)
  let ep : P ⋙ S ≅ W := lowerStarComp K c.g d.g
  have hn (L : HomotopyCategory
      (Sheaf c.restrict.Z.smallEtaleTopology K) (.up ℤ)) :=
    openExchangeDerivedUnit A (U := c.restrict.Z) (pullback.fst c.g d.i) c.restrict.g c.g d.i
      c.isPullback_restrict L
  have hχ (M : Sheaf c.restrict.Z.smallEtaleTopology K) :
      χ.app M ≫ P.map ((openImmersionLowerShriekToLowerStar K
          (pullback.fst c.g d.i)).app M) ≫
        (lowerStarComp K (pullback.fst c.g d.i) c.g (c.restrict.g ≫ d.i)
          c.isPullback_restrict.w).hom.app M =
      (openImmersionLowerShriekToLowerStar K d.i).app (R.obj M) ≫
        (lowerStarComp K c.restrict.g d.i).hom.app M := by
    rw [reassoc_of% (sheaf_exchange_inclusion A (pullback.fst c.g d.i)
      c.restrict.g c.g d.i c.isPullback_restrict M)]
    simp only [squareLowerStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc]
    erw [Iso.inv_hom_id_app]
    simp only [Category.comp_id]
    rfl
  let t : F ⋙ G ⟶ H ⋙ W :=
    Functor.whiskerRight ah.hom G ≫ Functor.whiskerLeft J (Functor.whiskerLeft R ae.hom) ≫
      Functor.whiskerLeft J (Functor.whiskerRight χ S) ≫
      Functor.whiskerLeft (J ⋙ O) ep.hom ≫ Functor.whiskerRight eo.inv W
  have ha := normalized_sheaf_tower A h e d c F G ah ae a na χ hχ
  have hd := canonical_derived_tower A h e d c
  rw [exactUnit_eq_nunit A c.restrict F ah, exactUnit_eq_nunit A d G ae,
    exactUnit_eq_nunit A (d.comp c) (F ⋙ G) a]
  change Functor.whiskerRight (nunit F J R ah.hom) G.mapDerivedCategory ≫
    Functor.whiskerLeft (J.mapDerivedCategory ⋙ R.rightDerivedFunctor) (nunit G I S ae.hom) ≫
      (rightDerivedLowerShriekOfCompactificationCompIso A d c).hom =
    (Functor.mapDerivedCategoryCompIso F G).hom ≫ nunit (F ⋙ G) H W a.hom
  rw [← ha, hd]
  exact normalizedDerivedUnitPasting J R I O P S H W F G ah.hom ae.hom χ Γ
    (fun L ↦ hn L) eo ep

end AlgebraicGeometry.Etale
