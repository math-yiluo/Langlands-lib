/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport
import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictReductionComposition
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenEndpointLimitTransport
import all WeilConjectures.AlgebraicGeometry.StrictTower.ScalarRestrictionOpenSupport
import WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenClopenProjector
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

/-!
# Strict reduction comparisons for completed operations

Strict reduction followed by constant-coefficient restriction compares completed-ring
objects with derived strict towers of constant-coefficient modules. This file records its
comparisons with inverse images.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8 (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The mate of a horizontally pasted square of isomorphisms is invertible when the mates of
the two pieces are. -/
theorem mateEquiv_isIso_of_paste {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : E ⥤ F} {R₃ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    (ρ : G₁ ⋙ L₂ ≅ L₁ ⋙ H₁) (ε : L₂ ⋙ H₂ ≅ G₂ ⋙ L₃)
    [IsIso (mateEquiv adj₁ adj₂ ρ.hom)] [IsIso (mateEquiv adj₂ adj₃ ε.inv)] :
    IsIso (mateEquiv adj₁ adj₃
      ((Functor.associator L₁ H₁ H₂).symm ≪≫ Functor.isoWhiskerRight ρ.symm H₂ ≪≫
        Functor.associator G₁ L₂ H₂ ≪≫
        Functor.isoWhiskerLeft G₁ ε ≪≫ (Functor.associator G₁ G₂ L₃).symm).inv) := by
  have h : ((Functor.associator L₁ H₁ H₂).symm ≪≫ Functor.isoWhiskerRight ρ.symm H₂ ≪≫
        Functor.associator G₁ L₂ H₂ ≪≫
        Functor.isoWhiskerLeft G₁ ε ≪≫ (Functor.associator G₁ G₂ L₃).symm).inv =
      TwoSquare.hComp (TwoSquare.mk _ _ _ _ ρ.hom) (TwoSquare.mk _ _ _ _ ε.inv) := by
    ext X
    simp [TwoSquare.hComp]
  rw [h, mateEquiv_vcomp adj₁ adj₂ adj₃]
  have h1 : IsIso (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ ρ.hom)) :=
    inferInstanceAs (IsIso (mateEquiv adj₁ adj₂ ρ.hom))
  have h2 : IsIso (mateEquiv adj₂ adj₃ (TwoSquare.mk _ _ _ _ ε.inv)) :=
    inferInstanceAs (IsIso (mateEquiv adj₂ adj₃ ε.inv))
  have : ∀ X, IsIso ((TwoSquare.vComp (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ ρ.hom))
      (mateEquiv adj₂ adj₃ (TwoSquare.mk _ _ _ _ ε.inv))).app X) := by
    intro X
    simp only [TwoSquare.vComp, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Morphism algebra deriving the comparison of a square from the comparisons of its two
composites. -/
theorem Functor.map_comp_eq_of_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {c₀ c₁ c₂ c₃ : C} {y z e₁ e₂ e₃ e₄ : D} {u : c₀ ⟶ c₂} {mh : c₁ ⟶ c₀} {mi : c₀ ⟶ c₁}
    {ah : c₂ ⟶ c₁} {q : c₁ ⟶ c₃} {p : c₃ ⟶ c₂} {s : F.obj c₁ ⟶ e₁} {t₁ : F.obj c₂ ⟶ y}
    {t₂ : y ⟶ e₂} {bh : e₂ ⟶ e₁} {q' : e₁ ⟶ e₄} {p' : e₄ ⟶ e₂} {w₁ : F.obj c₀ ⟶ z}
    {w₂ : z ⟶ e₃} {nh : e₁ ⟶ e₃} {ni : e₃ ⟶ e₁} {v : e₃ ⟶ e₂}
    (e₁' : u = (mi ≫ q) ≫ p) (e₂' : v = (ni ≫ q') ≫ p') (hm : mi ≫ mh = 𝟙 c₀)
    (ha : (q ≫ p) ≫ ah = 𝟙 c₁) (hb : bh ≫ q' ≫ p' = 𝟙 e₂) (hn : nh ≫ ni = 𝟙 e₁)
    (h₁ : F.map ah ≫ s = t₁ ≫ t₂ ≫ bh) (h₂ : F.map mh ≫ w₁ ≫ w₂ = s ≫ nh) :
    F.map u ≫ t₁ ≫ t₂ = w₁ ≫ w₂ ≫ v := by
  subst e₁' e₂'
  have ht : t₁ ≫ t₂ = F.map ah ≫ s ≫ q' ≫ p' := by
    rw [← Category.assoc, h₁]
    simp only [Category.assoc, hb, Category.comp_id]
  have hs : F.map mi ≫ s = w₁ ≫ w₂ ≫ ni := by
    calc F.map mi ≫ s = F.map mi ≫ s ≫ nh ≫ ni := by rw [hn, Category.comp_id]
      _ = F.map mi ≫ F.map mh ≫ w₁ ≫ w₂ ≫ ni := by rw [reassoc_of% h₂]
      _ = w₁ ≫ w₂ ≫ ni := by rw [← F.map_comp_assoc, hm, F.map_id, Category.id_comp]
  rw [ht, Category.assoc, F.map_comp, Category.assoc, ← F.map_comp_assoc, ← F.map_comp_assoc,
    Category.assoc, ha, F.map_comp, F.map_id, Category.comp_id, ← Category.assoc, hs]
  simp

/-- Morphism algebra combining the reduction and restriction composition coherences. -/
theorem Functor.strictPull_comp_algebra {T S S' : Type*} [Category T] [Category S]
    [Category S'] (F : T ⥤ S) (G : S' ⥤ S)
    {a₀ a₁ a₂ a₃ b : T} {c : S} {e₁ e₂ e₃ : S'}
    {pc : a₀ ⟶ a₁} {rfgH : b ⟶ a₀} {rfgI : a₀ ⟶ b} {rfH : a₂ ⟶ a₁} {rfI : a₁ ⟶ a₂}
    {tH : a₃ ⟶ a₂} {tI : a₂ ⟶ a₃} {D : b ⟶ a₃}
    {εf₁ : F.obj a₂ ⟶ G.obj e₁} {εf₂ : F.obj a₃ ⟶ G.obj e₂} {rg : e₁ ⟶ e₂} {εg : e₂ ⟶ e₃}
    {εfg : F.obj b ⟶ c} {gC : c ⟶ G.obj e₃}
    (hfg : rfgI ≫ rfgH = 𝟙 a₀) (hf : rfH ≫ rfI = 𝟙 a₂) (ht : tH ≫ tI = 𝟙 a₃)
    (hA : rfgH ≫ pc = D ≫ tH ≫ rfH)
    (nat : F.map tI ≫ εf₂ = εf₁ ≫ G.map rg)
    (hB : F.map D ≫ εf₂ ≫ G.map εg = εfg ≫ gC) :
    F.map pc ≫ (F.map rfI ≫ εf₁) ≫ G.map (rg ≫ εg) = (F.map rfgI ≫ εfg) ≫ gC := by
  have h1 : pc ≫ rfI = rfgI ≫ D ≫ tH := by
    calc pc ≫ rfI = (rfgI ≫ rfgH) ≫ pc ≫ rfI := by rw [hfg, Category.id_comp]
      _ = rfgI ≫ (rfgH ≫ pc) ≫ rfI := by simp only [Category.assoc]
      _ = rfgI ≫ D ≫ tH := by rw [hA]; simp only [Category.assoc, hf, Category.comp_id]
  have h2 : F.map tH ≫ εf₁ ≫ G.map rg = εf₂ := by
    rw [← nat, ← F.map_comp_assoc, ht, F.map_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, h1]
  simp only [F.map_comp, G.map_comp, Category.assoc]
  rw [reassoc_of% h2, hB]
end CategoryTheory

namespace CategoryTheory.ProperOpenTransport

/-- The open comparison is invertible when both open units are invertible and the target
lies in the essential image of the second open extension. -/
theorem openComparison_isIso_of_mem_essImage {U X U₁ X₁ : Type*} [Category U] [Category X]
    [Category U₁] [Category X₁] {Jj : U ⥤ X} {Pj : X ⥤ U} (adjJ : Jj ⊣ Pj)
    {Jj₁ : U₁ ⥤ X₁} {Pj₁ : X₁ ⥤ U₁} (adjJ₁ : Jj₁ ⊣ Pj₁) {ΦU : U ⥤ U₁} {ΦX : X ⥤ X₁}
    (φ : Pj ⋙ ΦU ≅ ΦX ⋙ Pj₁) [IsIso adjJ.unit] [IsIso adjJ₁.unit]
    (h : ∀ M, Jj₁.essImage (ΦX.obj (Jj.obj M))) :
    IsIso (openComparison adjJ adjJ₁ φ) := by
  have ff := adjJ₁.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h1 := unit_openComparison adjJ adjJ₁ φ M
  have : IsIso (Pj₁.map ((openComparison adjJ adjJ₁ φ).app M)) := by
    have : IsIso (adjJ₁.unit.app (ΦU.obj M) ≫
        Pj₁.map ((openComparison adjJ adjJ₁ φ).app M)) := by
      rw [← h1]
      infer_instance
    exact IsIso.of_isIso_comp_left (adjJ₁.unit.app (ΦU.obj M)) _
  have hc1 : IsIso (adjJ₁.counit.app (Jj₁.obj (ΦU.obj M))) :=
    adjJ₁.isIso_counit_app_iff_mem_essImage.mpr (Jj₁.obj_mem_essImage _)
  have hc2 : IsIso (adjJ₁.counit.app (ΦX.obj (Jj.obj M))) :=
    adjJ₁.isIso_counit_app_iff_mem_essImage.mpr (h M)
  have hn := adjJ₁.counit.naturality ((openComparison adjJ adjJ₁ φ).app M)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  have : IsIso (adjJ₁.counit.app (Jj₁.obj (ΦU.obj M)) ≫
      (openComparison adjJ adjJ₁ φ).app M) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left (adjJ₁.counit.app (Jj₁.obj (ΦU.obj M))) _

end CategoryTheory.ProperOpenTransport

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

/-- Restricting the action of a ring extension to constant coefficients preserves
open support. Source: Stacks 03DI (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem restrictScalars_openExtension_counit_isIso
    {B : Type (u + 1)} [CommRing B] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (RX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (RU : Sheaf (Scheme.ProEt.topology U) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj RX ≅ RU)
    (a : coefficients B X ⟶ RX) (M : Scheme.proEtaleRingModules U RU) :
    IsIso ((moduleJAdj.{u} B j).counit.app
      ((Scheme.proEtaleRingRestrictScalars a).obj
        ((Scheme.proEtaleRingOpenExtension j RX RU c).obj M))) := by
  obtain ⟨eA, ⟨hA⟩⟩ := Scheme.proEtaleOpen_slicePresentation j RX RU c
  obtain ⟨eB, ⟨hB⟩⟩ := Scheme.proEtaleOpen_slicePresentation j
    (coefficients B X) (coefficients B U) (constantRingIso B j)
  let RB := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (coefficients B X)
  let RA := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RX
  let ar : RB ⟶ RA := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a
  let W := Scheme.ProEt.mk j
  have : IsOpenImmersion W.hom := inferInstanceAs (IsOpenImmersion j)
  let N := (SheafOfModules.restrictScalars
    (((Scheme.ProEt.topology X).overPullback RingCat W).map ar)).obj (eA.functor.obj M)
  have : IsIso (SheafOfModules.localizedModuleAdjunctionIndependent
      (coefficients B X) W).unit := localizedOpen_unit_isIso W (coefficients B X)
  let ff := (SheafOfModules.localizedModuleAdjunctionIndependent
    (coefficients B X) W).fullyFaithfulLOfIsIsoUnit
  let ffB := ((Functor.FullyFaithful.ofFullyFaithful eB.functor).comp ff).ofIso hB.symm
  have : (moduleJ B j).Full := ffB.full
  have : (moduleJ B j).Faithful := ffB.faithful
  let q := (PresheafOfModules.sheafification.{u + 1} (𝟙 RB.obj)).mapIso
    (scalarExtensionPresheafIso ar W (eA.functor.obj M)) ≪≫
      scalarSheafificationIso ar
        (SheafOfModules.extensionByZeroPresheafObj.{u + 1} RA W (eA.functor.obj M))
  let t : (Scheme.proEtaleRingRestrictScalars a).obj
      ((Scheme.proEtaleRingOpenExtension j RX RU c).obj M) ≅
      (moduleJ B j).obj (eB.inverse.obj N) :=
    (Scheme.proEtaleRingRestrictScalars a).mapIso (hA.app M) ≪≫ q.symm ≪≫
      (SheafOfModules.localizedModuleExtension (coefficients B X) W).mapIso
        (eB.counitIso.app N).symm ≪≫ (hB.app (eB.inverse.obj N)).symm
  exact (moduleJAdj B j).isIso_counit_app_of_iso t

end AlgebraicGeometry.ProEtale.StrictTower

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian
  SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedLocalEquivalences

attribute [local instance 100000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

/-- Strict reduction followed by constant-coefficient restriction: the comparison of
completed-ring objects with derived strict towers of constant-coefficient modules.
Source: blueprint step 8 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
def cbcStrictReduction (T : Scheme.{t}) :
    DerivedCategory (proEtaleRingModules T (d.completedRing T)) ⥤
      ProEtale.StrictTower.Derived A T :=
  completedReductionTower T d ⋙ exchangeTowerRes d T

theorem cbcStrictReduction_map {T : Scheme.{t}} {K L : d.derived T} (f : K ⟶ L) :
    (cbcStrictReduction d T).map f =
      (exchangeTowerRes d T).map ((completedReductionTower T d).map f) := rfl

theorem cbcStrictReduction_obj {T : Scheme.{t}} (K : d.derived T) :
    (cbcStrictReduction d T).obj K =
      (exchangeTowerRes d T).obj ((completedReductionTower T d).obj K) := rfl

/-- Strict reduction commutes with inverse image: the normalized reduction/pullback
comparison followed by the restriction/pullback comparison.
Source: blueprint step 8 (blueprint: proposition-composition-base-change-rf-shriek--4). -/
def cbcStrictPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.pull f ⋙ cbcStrictReduction d U ≅
      cbcStrictReduction d V ⋙ ProEtale.StrictTower.G A f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.reductionTowerPullbackIso f).symm (exchangeTowerRes d U) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (completedReductionTower V d) (exchangeResPull d f) ≪≫
    (Functor.associator _ _ _).symm

theorem cbcStrictPull_hom_app {U V : Scheme.{t}} (f : U ⟶ V) (M : d.derived V) :
    (cbcStrictPull d f).hom.app M =
      (exchangeTowerRes d U).map ((d.reductionTowerPullbackIso f).inv.app M) ≫
        (exchangeResPull d f).hom.app ((completedReductionTower V d).obj M) := by
  simp only [cbcStrictPull, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id]
  erw [Category.id_comp]
/-- Strict reduction commutes with inverse image compatibly with composition: the
comparison for a composite is the composite of the comparisons, up to the completed and
strict inverse-image compositors.
Source: blueprint step 8; Stacks 0D6D (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictPull_comp {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : d.derived Z) :
    (cbcStrictReduction d X).map ((d.pullComp f g).hom.app M) ≫
        (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
          (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) =
      (cbcStrictPull d (f ≫ g)).hom.app M ≫
        (ProEtale.StrictTower.gComp A f g).hom.app ((cbcStrictReduction d Z).obj M) := by
  obtain ⟨κ, hκ₁, hκ₂⟩ := d.pullComp_eq_triangle f g
  have hA := reductionTowerPullbackIso_comp d f g κ hκ₁ M
  have hB := exchangeResPull_comp d f g κ hκ₂ ((completedReductionTower Z d).obj M)
  have nat := (exchangeResPull d f).hom.naturality ((d.reductionTowerPullbackIso g).inv.app M)
  rw [cbcStrictPull_hom_app, cbcStrictPull_hom_app, cbcStrictPull_hom_app,
    cbcStrictReduction_map]
  exact Functor.strictPull_comp_algebra (exchangeTowerRes d X)
    (ProEtale.StrictTower.G A f) (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app]; erw [CategoryTheory.Functor.map_id]; rfl)
    hA nat hB

/-- The comparisons for equal morphisms agree up to the equality transports. -/
theorem cbcStrictPull_eqToHom {X Z : Scheme.{t}} {f₁ f₂ : X ⟶ Z} (e : f₁ = f₂)
    (M : d.derived Z) :
    (cbcStrictReduction d X).map ((eqToHom (congrArg (fun f ↦ d.pull f) e)).app M) ≫
        (cbcStrictPull d f₂).hom.app M =
      (cbcStrictPull d f₁).hom.app M ≫
        (eqToHom (congrArg (ProEtale.StrictTower.G A) e)).app ((cbcStrictReduction d Z).obj M) := by
  subst e
  simp

/-- The comparison for a composite, through an equality of the composite. -/
theorem cbcStrictPull_comp_eq {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) {q : X ⟶ Z}
    (e : f ≫ g = q) (M : d.derived Z) :
    (cbcStrictReduction d X).map ((d.pullComp f g).inv.app M ≫
        (eqToIso (congrArg (fun f ↦ d.pull f) e.symm)).inv.app M) ≫
          (cbcStrictPull d q).hom.app M =
      (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
        (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) ≫
          ((ProEtale.StrictTower.gComp A f g).inv ≫
            (eqToIso (congrArg (ProEtale.StrictTower.G A) e.symm)).inv).app
              ((cbcStrictReduction d Z).obj M) := by
  subst e
  have hc := cbcStrictPull_comp d f g M
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  rw [← cancel_epi ((cbcStrictReduction d X).map ((d.pullComp f g).hom.app M)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, ← Category.assoc ((cbcStrictPull d f).hom.app _),
    ← Category.assoc ((cbcStrictReduction d X).map _), hc]
  simp

/-- The comparison for a composite, with the compositors packaged as isomorphisms. -/
theorem cbcStrictPull_comp_hom {X Y Z : Scheme.{t}} (f : X ⟶ Y) (g : Y ⟶ Z) {q : X ⟶ Z}
    (e : f ≫ g = q) (M : d.derived Z) :
    (cbcStrictReduction d X).map (((d.pullComp f g).symm ≪≫
        eqToIso (congrArg (fun f ↦ d.pull f) e)).hom.app M) ≫
          (cbcStrictPull d q).hom.app M =
      (cbcStrictPull d f).hom.app ((d.pull g).obj M) ≫
        (ProEtale.StrictTower.G A f).map ((cbcStrictPull d g).hom.app M) ≫
          ((ProEtale.StrictTower.gComp A f g).symm ≪≫
            eqToIso (congrArg (ProEtale.StrictTower.G A) e)).hom.app
              ((cbcStrictReduction d Z).obj M) := by
  subst e
  have hc := cbcStrictPull_comp_eq d f g rfl M
  simpa using hc

/-- The comparisons are compatible with the inverse-image square of a commutative square. -/
theorem cbcStrictPull_square {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) (x : d.derived T) :
    (cbcStrictReduction d V).map ((cbcSquarePull d k r p i h).inv.app x) ≫
        (cbcStrictPull d r).hom.app ((d.pull i).obj x) ≫
          (ProEtale.StrictTower.G A r).map ((cbcStrictPull d i).hom.app x) =
      (cbcStrictPull d k).hom.app ((d.pull p).obj x) ≫
        (ProEtale.StrictTower.G A k).map ((cbcStrictPull d p).hom.app x) ≫
          (ProEtale.StrictTower.squareG A k r p i h).inv.app
            ((cbcStrictReduction d T).obj x) := by
  have e1a : (cbcSquarePull d k r p i h).inv = ((d.pullComp k p).inv ≫
      (eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).inv) ≫ (d.pullComp r i).hom := rfl
  have e1 : (cbcSquarePull d k r p i h).inv.app x = ((d.pullComp k p).inv.app x ≫
      (eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).inv.app x) ≫ (d.pullComp r i).hom.app x := by
    rw [e1a, NatTrans.comp_app, NatTrans.comp_app]
  have ha0 : (eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).inv ≫ (d.pullComp r i).hom =
      ((d.pullComp r i).symm ≪≫ eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).inv := rfl
  have ha : ((eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).inv.app x ≫
      (d.pullComp r i).hom.app x) ≫
        ((d.pullComp r i).symm ≪≫ eqToIso (congrArg (fun f ↦ d.pull f) h.symm)).hom.app x =
      𝟙 _ := by
    rw [← NatTrans.comp_app, ha0, Iso.inv_hom_id_app]
  have e2a : (ProEtale.StrictTower.squareG A k r p i h).inv =
      ((ProEtale.StrictTower.gComp A k p).inv ≫
        (eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).inv) ≫
          (ProEtale.StrictTower.gComp A r i).hom := rfl
  have e2 : (ProEtale.StrictTower.squareG A k r p i h).inv.app ((cbcStrictReduction d T).obj x) =
      ((ProEtale.StrictTower.gComp A k p).inv.app ((cbcStrictReduction d T).obj x) ≫
        (eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).inv.app
          ((cbcStrictReduction d T).obj x)) ≫
        (ProEtale.StrictTower.gComp A r i).hom.app ((cbcStrictReduction d T).obj x) := by
    rw [e2a, NatTrans.comp_app, NatTrans.comp_app]
  have hb0 : (eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).inv ≫
      (ProEtale.StrictTower.gComp A r i).hom =
      ((ProEtale.StrictTower.gComp A r i).symm ≪≫
        eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).inv := rfl
  have hb : ((ProEtale.StrictTower.gComp A r i).symm ≪≫
        eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).hom.app
          ((cbcStrictReduction d T).obj x) ≫
      (eqToIso (congrArg (ProEtale.StrictTower.G A) h.symm)).inv.app
          ((cbcStrictReduction d T).obj x) ≫
        (ProEtale.StrictTower.gComp A r i).hom.app ((cbcStrictReduction d T).obj x) = 𝟙 _ := by
    rw [← NatTrans.comp_app, hb0, Iso.hom_inv_id_app]
  exact Functor.map_comp_eq_of_comp (cbcStrictReduction d V) e1 e2 (Iso.inv_hom_id_app _ _)
    ha hb (Iso.hom_inv_id_app _ _)
    (cbcStrictPull_comp_hom d r i h.symm x) (cbcStrictPull_comp d k p x)

/-- The mate of the reduction/pullback comparison is the strict projection-formula map, so it
is invertible. Source: blueprint step 8 (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem reductionTowerPullbackIso_mate_isIso {U V : Scheme.{t}} (f : U ⟶ V) :
    IsIso (mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom) := by
  have h (K : d.derived U) : (mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom).app K = d.towerProjection f K := by
    rw [AdicCoefficientDatum.towerProjection, Adjunction.homEquiv_unit]
    simp [mateEquiv_apply]
  have (K : d.derived U) : IsIso ((mateEquiv (cbcPullPushAdjunction d f) (d.towerAdjunction f)
      (d.reductionTowerPullbackIso f).hom).app K) := by
    rw [h K]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- The mate of the restriction/pullback comparison is the restriction/direct-image
comparison, so it is invertible. Source: blueprint step 8; Stacks 0D6E
(blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem exchangeResPull_mate_isIso {U V : Scheme.{t}} (f : U ⟶ V) :
    IsIso (mateEquiv (d.towerAdjunction f) (ProEtale.StrictTower.adj A f)
      (exchangeResPull d f).inv) := by
  have hs := (exchangeResPush_existsUnique d f).choose_spec.1
  unfold ExchangeResPushNormalized at hs
  have he := exactDerivedMate_eq (d.towerModuleAdjunction f)
    (exchangeTowerModuleAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) (exchangeModuleResPull d f).symm (exchangeModuleResPush d f)
    (exchangeModuleResPull_mate d f) (exchangeResPush d f) hs
  have h : IsIso (exactDerivedMate (d.towerModuleAdjunction f)
    (exchangeTowerModuleAdjunction f (exchangeConstantRing V A) (exchangeConstantRing U A)
      (exchangeConstantIso f A)) (exchangeModuleResPull d f).symm) := by
    rw [← he]
    infer_instance
  rw [exactDerivedMate, Functor.mapDerivedCategorySquareIso_symm] at h
  exact h

/-- Strict reduction commutes with direct image: the mate of the inverse-image comparison
is invertible. Its components are the strict projection-formula map and the
restriction/direct-image comparison.
Source: blueprint step 8; Stacks 0D6E (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictPush_isIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    IsIso (mateEquiv (cbcPullPushAdjunction d f) (ProEtale.StrictTower.adj A f)
      (cbcStrictPull d f).inv) := by
  have := reductionTowerPullbackIso_mate_isIso d f
  have := exchangeResPull_mate_isIso d f
  exact mateEquiv_isIso_of_paste (cbcPullPushAdjunction d f) (d.towerAdjunction f)
    (ProEtale.StrictTower.adj A f) (d.reductionTowerPullbackIso f) (exchangeResPull d f)

/-- Restriction to constant coefficients commutes with ordinary open extension.
Source: Stacks 03DI (blueprint: proposition-composition-base-change-rf-shriek--4). -/
private theorem exchangeOpen_isIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (ProperOpenTransport.openComparison (cbcEndpointOpenAdj d j)
      (ProEtale.StrictTower.moduleJAdj A j) (exchangeOrdinaryResPull d j)) := by
  obtain ⟨hfull, hfaith⟩ := cbcEndpointOpen_fullFaithful d j
  have : IsIso (cbcEndpointOpenAdj d j).unit := inferInstance
  have := ProEtale.StrictTower.clopenModule_openUnit_isIso (B := A) j
  refine ProperOpenTransport.openComparison_isIso_of_mem_essImage _ _ _ fun M ↦ ?_
  have ff := (ProEtale.StrictTower.moduleJAdj A j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  exact (ProEtale.StrictTower.moduleJAdj A j).isIso_counit_app_iff_mem_essImage.mp
    (ProEtale.StrictTower.restrictScalars_openExtension_counit_isIso j _ _
      (d.integralRingIso j) (exchangeScalar d X) M)

/-- Restriction to constant coefficients commutes with open extension of derived strict
towers. Source: Stacks 03DI (blueprint: proposition-composition-base-change-rf-shriek--4). -/
private def exchangeTowerOpenIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    exchangeTowerRes d U ⋙ ProEtale.StrictTower.J A j ≅
      cbcTowerDerived (cbcEndpointOpen d j) ⋙ exchangeTowerRes d X :=
  have := exchangeOpen_isIso d j
  Functor.mapDerivedCategorySquareIso
    (Functor.whiskeringRightObjCompIso (proEtaleRingRestrictScalars (exchangeScalar d U))
        (ProEtale.StrictTower.moduleJ A j) ≪≫
      (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (asIso (ProperOpenTransport.openComparison
        (cbcEndpointOpenAdj d j) (ProEtale.StrictTower.moduleJAdj A j)
        (exchangeOrdinaryResPull d j))) ≪≫
      (Functor.whiskeringRightObjCompIso (cbcEndpointOpen d j)
        (proEtaleRingRestrictScalars (exchangeScalar d X))).symm)

/-- Strict reduction commutes with extension by zero: the open-extension mate of the
inverse-image comparison is invertible.
Source: blueprint step 8; Stacks 03DI (blueprint:
proposition-composition-base-change-rf-shriek--4). -/
theorem cbcStrictOpen_isIso {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (CategoryTheory.ProperOpenTransport.openComparison (cbcDerivedOpenAdjunction d j)
      (ProEtale.StrictTower.jAdj A j) (cbcStrictPull d j)) := by
  have := cbcOpenUnit_isIso d j
  have := ProEtale.StrictTower.jAdj_unit_isIso A j
  refine ProperOpenTransport.openComparison_isIso_of_mem_essImage _ _ _ fun M ↦ ?_
  have hr := (cbcEndpointReductionInv_properties d j).1 M
  let e₁ := (cbcDerivedOpenAdjunction d j).leftAdjointUniq (cbcEndpointDerivedOpenAdj d j)
  exact Functor.essImage.ofIso
    ((exchangeTowerOpenIso d j).app ((completedReductionTower U d).obj M) ≪≫
      (exchangeTowerRes d X).mapIso ((asIso (cbcEndpointReductionInv d j M)) ≪≫
        (completedReductionTower X d).mapIso (e₁.app M).symm))
    (Functor.obj_mem_essImage _ _)

end AlgebraicGeometry.Scheme
