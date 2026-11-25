/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.Adjunction.ConjugatePaste
import all WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperIntegralRationalScalarComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Compact-support identity and shift calculations

The proved generic identity and shift helpers used by compact-support projection
are kept together here so the geometric file compiles within its time limit.
(blueprint: lem-pur-compact-support-identity-calculus).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.privateModule false
set_option linter.unusedSimpArgs false
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj

/- Canonical derived-unit factorization detects each comparison shift square on
K-injective representatives. The helper theorems are registered only within the proof. -/
private theorem rightComparison_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (G : DerivedCategory C ⥤ DerivedCategory D)
    [G.CommShift ℤ]
    (β : F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ G)
    [NatTrans.CommShift β ℤ] (τ : F.rightDerivedFunctor ⟶ G)
    (h : F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh τ = β) :
    NatTrans.CommShift τ ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun X ↦ by
      obtain ⟨K, _, rfl⟩ := HomotopyCategory.KInjectives.mk_surjective X
      dsimp
      infer_instance)
  have : NatTrans.CommShift
      (F.rightDerivedFunctorUnit ≫ Functor.whiskerLeft DerivedCategory.Qh τ) ℤ := by
    rw [h]
    infer_instance
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh F.rightDerivedFunctorUnit τ

private theorem rightNatIso_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G) :
    NatTrans.CommShift (Functor.rightDerivedFunctorNatIso e).hom ℤ := by
  have : NatTrans.CommShift G.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift G
  apply rightComparison_shift F _
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh ≫ G.rightDerivedFunctorUnit) _
  exact Functor.rightDerivedNatTrans_fac _ _ _ _
    (HomotopyCategory.quasiIso C (.up ℤ)) _

private theorem rightExactIso_shift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    NatTrans.CommShift F.rightDerivedFunctorIsoMapDerivedCategory.hom ℤ := by
  apply rightComparison_shift F _ F.mapDerivedCategoryFactorsh.inv _
  exact F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac

private theorem rightCompIso_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesKInjectiveComplexes] :
    NatTrans.CommShift (Functor.rightDerivedFunctorCompIso F G).hom ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift G.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift G
  apply rightComparison_shift (F ⋙ G) _ (Functor.rightDerivedFunctorCompUnit F G) _
  simp [Functor.rightDerivedFunctorCompIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso]

private theorem rightCompExactIso_shift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    NatTrans.CommShift (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F G).hom ℤ := by
  have : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ :=
    CategoryTheory.canonical_unit_commShift F
  have : NatTrans.CommShift
      (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G) ℤ := by
    dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
    infer_instance
  apply rightComparison_shift (F ⋙ G) _
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F G) _
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso]

private theorem inverseConjugate_shift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (ad₁ : L₁ ⊣ R₁) (ad₂ : L₂ ⊣ R₂)
    [L₁.CommShift ℤ] [L₂.CommShift ℤ] [R₁.CommShift ℤ] [R₂.CommShift ℤ]
    [ad₁.CommShift ℤ] [ad₂.CommShift ℤ]
    (e : R₁ ≅ R₂) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (((conjugateIsoEquiv ad₁ ad₂).symm e).hom) ℤ := by
  dsimp [conjugateIsoEquiv, conjugateEquiv, mateEquiv, Iso.homCongr,
    TwoSquare.mk]
  infer_instance

private theorem identity_comparison
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    {F F' : C ⥤ D} {L : D ⥤ D} (h : F' = F) (τ : F' ⟶ F ⋙ L)
    (idIso : L ≅ 𝟭 D)
    (hτ : ∀ M, τ.app M ≫ idIso.hom.app (F.obj M) =
      eqToHom (congrArg (fun V : C ⥤ D ↦ V.obj M) h)) :
    eqToHom h.symm ≫ τ = (Functor.rightUnitor F).inv ≫
      Functor.whiskerLeft F idIso.inv := by
  subst h
  ext M
  apply (cancel_mono (idIso.hom.app (F'.obj M))).1
  simpa only [NatTrans.comp_app, eqToHom_refl, NatTrans.id_app,
    Category.id_comp, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app, Functor.id_obj] using hτ M

private theorem restriction_identity_component
    {C D : Type*} [Category C] [Category D]
    {P R : C ⥤ C} (ad : P ⊣ R) (e : P ≅ 𝟭 C)
    (U U' : C ⥤ D) (h : U' = U) (τ : U' ≅ P ⋙ U)
    (hτ : ∀ M, τ.hom.app M ≫ U.map (e.hom.app M) =
      eqToHom (congrArg (fun V : C ⥤ D ↦ V.obj M) h)) (M : C) :
    (eqToIso h.symm ≪≫ τ).hom.app (R.obj M) ≫ U.map (ad.counit.app M) =
      U.map ((conjugateIsoEquiv ad Adjunction.id e.symm).hom.app M) := by
  subst U'
  have ha (N : C) : τ.hom.app N = U.map (e.inv.app N) := by
    apply (Iso.comp_hom_eq_id (U.mapIso (e.app N))).1
    change τ.hom.app N ≫ U.map (e.hom.app N) = 𝟙 (U.obj N)
    exact hτ N
  simp only [eqToIso_refl, Iso.refl_trans]
  rw [ha, ← U.map_comp]
  congr 1
  exact (conjugateEquiv_adjunction_id ad e.inv M).symm

section IdentityProofHelpers
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem scalar_unit_normalization
    {C : Type*} [Category C] {L R : C ⥤ C} (ad : L ⊣ R) (ρ : R ≅ 𝟭 C)
    (X : C) :
    ad.unit.app X ≫ R.map
      ((ad.leftAdjointUniq (Adjunction.id.ofNatIsoRight ρ.symm)).hom.app X) =
        ρ.inv.app X := by
  simpa only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.id_unit, NatTrans.id_app, Category.id_comp,
    Iso.symm_hom, Functor.id_obj] using ad.unit_leftAdjointUniq_hom_app
      (Adjunction.id.ofNatIsoRight ρ.symm) X

private theorem scalar_open_identity
    {C D : Type*} [Category C] [Category D]
    {L R : C ⥤ C} {L' R' : D ⥤ D} {J : C ⥤ D} {U : D ⥤ C}
    (ad : L ⊣ R) (ad' : L' ⊣ R') (aj : J ⊣ U)
    (ρ : R ≅ 𝟭 C) (σ : R' ≅ 𝟭 D)
    (unitIso : L ≅ 𝟭 C) (unitIso' : L' ≅ 𝟭 D)
    (hunitIso : ∀ X, ad.unit.app X ≫ R.map (unitIso.hom.app X) = ρ.inv.app X)
    (hunitIso' : ∀ X, ad'.unit.app X ≫ R'.map (unitIso'.hom.app X) = σ.inv.app X)
    (e : U ⋙ R ≅ R' ⋙ U)
    (he : ∀ X, e.hom.app X ≫ U.map (σ.hom.app X) = ρ.hom.app (U.obj X))
    (X : C) :
    (((conjugateIsoEquiv (ad.comp aj) (aj.comp ad')).symm e).hom.app X) ≫
        J.map (unitIso.hom.app X) =
      unitIso'.hom.app (J.obj X) := by
  apply ((aj.comp ad').homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  have ht := unit_conjugateEquiv_symm (ad.comp aj) (aj.comp ad') e.hom X
  change (ad.comp aj).unit.app X ≫ e.hom.app ((L ⋙ J).obj X) =
    (aj.comp ad').homEquiv _ _
      (((conjugateIsoEquiv (ad.comp aj) (aj.comp ad')).symm e).hom.app X) at ht
  rw [← ht]
  have hid : (aj.comp ad').homEquiv X (J.obj X)
      (unitIso'.hom.app (J.obj X)) =
        aj.unit.app X ≫ U.map (σ.inv.app (J.obj X)) := by
    rw [Adjunction.comp_homEquiv]
    change aj.homEquiv _ _ (ad'.homEquiv _ _ _) = _
    rw [aj.homEquiv_unit, ad'.homEquiv_unit, hunitIso']
  dsimp only [Functor.id_obj]
  rw [hid]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    Category.assoc]
  rw [show e.hom.app (J.obj (L.obj X)) ≫ U.map (R'.map (J.map
      (unitIso.hom.app X))) =
      R.map (U.map (J.map
        (unitIso.hom.app X))) ≫
          e.hom.app (J.obj X) from (e.hom.naturality _).symm]
  have hj := aj.unit.naturality
    (unitIso.hom.app X)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_map] at hj
  rw [← R.map_comp_assoc, ← hj, R.map_comp]
  simp only [← Category.assoc]
  rw [hunitIso]
  simp only [Category.assoc]
  rw [← Category.assoc]
  rw [show ρ.inv.app X ≫ R.map (aj.unit.app X) =
      aj.unit.app X ≫ ρ.inv.app (U.obj (J.obj X)) from (ρ.inv.naturality _).symm]
  rw [Category.assoc]
  congr 1
  apply (cancel_mono (U.map (σ.hom.app (J.obj X)))).1
  rw [Category.assoc, he, Iso.inv_hom_id_app, ← U.map_comp,
    Iso.inv_hom_id_app]
  exact (U.map_id (J.obj X)).symm
section IdentitySquares
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [CategoryTheory.Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive]
  (R : C ⥤ C) (S : D ⥤ D) [R.Additive] [S.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [R.PreservesKInjectiveComplexes]
  (ρ : R ≅ 𝟭 C) (σ : S ≅ 𝟭 D) (e : F ⋙ S ≅ R ⋙ F)

private def derivedIdentity {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {T : A ⥤ A} [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (t : T ≅ 𝟭 A) : T.mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso t ≪≫ Functor.mapDerivedCategoryIdIso A

end IdentitySquares
end IdentityProofHelpers

namespace WeilConjectures.CompactSupportCondensedRealization

section CoefficientCompositionHelpers
set_option backward.defeqAttrib.useBackward false
private theorem scalarComp_eq_conjugate
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {M : B ⥤ C} {S : C ⥤ B}
    {N : A ⥤ C} {T : C ⥤ A}
    (ad : L ⊣ R) (bd : M ⊣ S) (cd : N ⊣ T) (ρ : S ⋙ R ≅ T) :
    (ad.comp bd).leftAdjointUniq (cd.ofNatIsoRight ρ.symm) =
      (conjugateIsoEquiv cd (ad.comp bd)).symm ρ.symm := by
  apply Iso.ext
  ext X
  apply ((ad.comp bd).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  simpa only [Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, conjugateIsoEquiv_symm_apply_hom] using
    unit_conjugateEquiv_symm cd (ad.comp bd) ρ.inv X

section AbstractPasting
variable {A B C D E F : Type*}
  [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
  {LX : A ⥤ B} {UX : B ⥤ A} {MX : B ⥤ C} {VX : C ⥤ B}
  {LY : D ⥤ E} {UY : E ⥤ D} {MY : E ⥤ F} {VY : F ⥤ E}
  {NX : A ⥤ C} {WX : C ⥤ A} {NY : D ⥤ F} {WY : F ⥤ D}
  (ax : LX ⊣ UX) (bx : MX ⊣ VX) (cx : NX ⊣ WX)
  (ay : LY ⊣ UY) (by' : MY ⊣ VY) (cy : NY ⊣ WY)
  {G : A ⥤ D} {H : B ⥤ E} {I : C ⥤ F}
  (ka : H ⋙ UY ≅ UX ⋙ G) (kb : I ⋙ VY ≅ VX ⋙ H)
  (kc : I ⋙ WY ≅ WX ⋙ G)
  (rx : WX ≅ VX ⋙ UX) (ry : WY ≅ VY ⋙ UY)

-- Conjugate the restriction compositors and paste the two extension mates.
private theorem push_pasting_canonical
    (hc : Functor.whiskerRight kb.hom UY ≫ Functor.whiskerLeft VX ka.hom ≫
        Functor.whiskerRight rx.inv G =
      Functor.whiskerLeft I ry.inv ≫ kc.hom) :
    let ex := (ax.comp bx).leftAdjointUniq (cx.ofNatIsoRight rx)
    let ey := (ay.comp by').leftAdjointUniq (cy.ofNatIsoRight ry)
    ∀ K : A,
      ey.hom.app (G.obj K) ≫ (Adjunction.pushHomOfComapIso cx cy kc).app K =
        MY.map ((Adjunction.pushHomOfComapIso ax ay ka).app K) ≫
          (Adjunction.pushHomOfComapIso bx by' kb).app (LX.obj K) ≫
          I.map (ex.hom.app K) := by
  dsimp only
  have hxcomp := scalarComp_eq_conjugate ax bx cx rx.symm
  have hycomp := scalarComp_eq_conjugate ay by' cy ry.symm
  simp only [Iso.symm_symm_eq] at hxcomp hycomp
  rw [hxcomp, hycomp]
  let ex := (conjugateIsoEquiv cx (ax.comp bx)).symm rx
  let ey := (conjugateIsoEquiv cy (ay.comp by')).symm ry
  change ∀ K : A, ey.hom.app (G.obj K) ≫ _ = _
  let α := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso ax ay ka)
  let β := TwoSquare.mk _ _ _ _ (Adjunction.pushHomOfComapIso bx by' kb)
  let gamma := ((TwoSquare.vComp α β).whiskerRight ey.inv).whiskerLeft ex.hom
  have he : mateEquiv cx cy gamma = TwoSquare.mk _ _ _ _ kc.inv := by
    have ha : mateEquiv ax ay α = TwoSquare.mk _ _ _ _ ka.inv :=
      (mateEquiv ax ay).apply_symm_apply _
    have hb : mateEquiv bx by' β = TwoSquare.mk _ _ _ _ kb.inv :=
      (mateEquiv bx by').apply_symm_apply _
    have hx : conjugateEquiv cx (ax.comp bx) ex.hom = rx.hom :=
      (conjugateEquiv cx (ax.comp bx)).apply_symm_apply _
    have hy : conjugateEquiv (ay.comp by') cy ey.inv = ry.inv :=
      (conjugateEquiv (ay.comp by') cy).apply_symm_apply _
    change mateEquiv cx cy
      (((α.vComp β).whiskerRight ey.inv).whiskerLeft ex.hom) = _
    rw [conjugateEquiv_mateEquiv_vcomp cx (ax.comp bx) cy,
      mateEquiv_conjugateEquiv_vcomp (ax.comp bx) (ay.comp by') cy,
      mateEquiv_hcomp ax ay bx by', ha, hb, hx, hy]
    ext K
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    apply (cancel_mono (kc.hom.app K)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hcK := congr_app hc K
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hcK
    rw [← hcK]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← G.map_comp, Iso.hom_inv_id_app, G.map_id]
    rfl
  have hgamma : gamma = Adjunction.pushHomOfComapIso cx cy kc :=
    ((mateEquiv cx cy).injective
      (he.trans ((mateEquiv cx cy).apply_symm_apply _).symm))
  intro K
  have hh := congr_app hgamma K
  dsimp [gamma, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, α, β] at hh
  simp only [Category.id_comp, Category.comp_id] at hh
  rw [← hh]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  rfl
end AbstractPasting

end CoefficientCompositionHelpers

private theorem diagonal_unique_mixed_injective
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    (F A B : C ⥤ D) (β : A ⟶ B) {M X Y : C}
    (i : X ⟶ M) (p : M ⟶ X) (j : Y ⟶ M) (q : M ⟶ Y)
    (hip : i ≫ p = 𝟙 X) (hjq : j ≫ q = 𝟙 Y)
    (z0 : F.obj M ⟶ B.obj M)
    (hu : ∃! e : F.obj M ⟶ A.obj M, e ≫ β.app M = z0) :
    Function.Injective (fun e : F.obj X ⟶ A.obj Y ↦ e ≫ β.app Y) := by
  intro a b hab
  obtain ⟨e, he, hu⟩ := hu
  let δ := F.map p ≫ (a - b) ≫ A.map j
  have hδ : δ ≫ β.app M = 0 := by
    dsimp only [δ]
    rw [Category.assoc, Category.assoc, β.naturality j, ← Category.assoc (a - b),
      Preadditive.sub_comp, sub_eq_zero.mpr hab, zero_comp, comp_zero]
  have heδ : e + δ = e := hu _ (by
    change (e + δ) ≫ β.app M = z0
    rw [Preadditive.add_comp, he, hδ, add_zero])
  have hz : δ = 0 := (add_left_cancel (heδ.trans (add_zero e).symm))
  have h := congrArg (fun z ↦ F.map i ≫ z ≫ A.map q) hz
  have hz' : a - b = 0 := by
    simpa only [δ, Category.assoc, ← F.map_comp_assoc, hip, F.map_id, Category.id_comp,
      ← A.map_comp, hjq, A.map_id, Category.comp_id, comp_zero, zero_comp] using h
  exact sub_eq_zero.mp hz'

private theorem normalized_lift_naturality
    {C D : Type*} [Category C] [Category D] [Preadditive C]
    {L : C ⥤ D} {U : D ⥤ C} (ad : L ⊣ U) (A : C ⥤ D) (B : C ⥤ C)
    (β : A ⋙ U ⟶ B) (σ : 𝟭 C ⟶ B) {X Y M : C}
    (i : X ⟶ M) (p : M ⟶ X) (j : Y ⟶ M) (q : M ⟶ Y)
    (hip : i ≫ p = 𝟙 X) (hjq : j ≫ q = 𝟙 Y) (v : X ⟶ Y)
    (hu : ∃! z : M ⟶ (A ⋙ U).obj M, z ≫ β.app M = σ.app M)
    (eX : L.obj X ⟶ A.obj X) (eY : L.obj Y ⟶ A.obj Y)
    (hX : ad.homEquiv _ _ eX ≫ β.app X = σ.app X)
    (hY : ad.homEquiv _ _ eY ≫ β.app Y = σ.app Y) :
    L.map v ≫ eY = eX ≫ A.map v := by
  apply (ad.homEquiv _ _).injective
  apply diagonal_unique_mixed_injective (𝟭 _) (A ⋙ U) B β i p j q hip hjq _ hu
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  have hb : U.map (A.map v) ≫ β.app Y = β.app X ≫ B.map v := β.naturality v
  rw [hY, hb, ← Category.assoc, hX]
  exact σ.naturality v

private theorem normalized_lift_naturality_of_unique
    {C D : Type*} [Category C] [Category D] [Preadditive C]
    {L : C ⥤ D} {U : D ⥤ C} (ad : L ⊣ U) (A : C ⥤ D) (B : C ⥤ C)
    (β : A ⋙ U ⟶ B) (σ : 𝟭 C ⟶ B) {X Y M : C}
    (i : X ⟶ M) (p : M ⟶ X) (j : Y ⟶ M) (q : M ⟶ Y)
    (hip : i ≫ p = 𝟙 X) (hjq : j ≫ q = 𝟙 Y) (v : X ⟶ Y)
    (hu : ∃! e : L.obj M ⟶ A.obj M,
      ad.homEquiv _ _ e ≫ β.app M = σ.app M)
    (eX : L.obj X ⟶ A.obj X) (eY : L.obj Y ⟶ A.obj Y)
    (hX : ad.homEquiv _ _ eX ≫ β.app X = σ.app X)
    (hY : ad.homEquiv _ _ eY ≫ β.app Y = σ.app Y) :
    L.map v ≫ eY = eX ≫ A.map v := by
  exact normalized_lift_naturality ad A B β σ i p j q hip hjq v
    ((ad.homEquiv _ _).existsUnique_congr_right.mp hu) eX eY hX hY

end WeilConjectures.CompactSupportCondensedRealization
