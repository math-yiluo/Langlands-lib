/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationCoefficientActions
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationRing
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedBelowCountableHomContinuity
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import WeilConjectures.CategoryTheory.ProperBaseChange.SequenceRelativeHomTelescope
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.RingTheory.Flat.Localization

import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnderlyingTelescope
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Scalar localization of shifted derived Hom

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 6.8.12 and
Proposition 6.8.14(2), with the abstract bounded-below telescope argument
(blueprint: lem-weil-pbc-scalar-localization-derived-hom).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w x y uB vB uT vT

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

open MonoidalCategory

namespace CategoryTheory

attribute [local irreducible] SheafOfModules.monoidalCategory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- Linear equivalences from the existing fraction quotient, using its canonical
localized scalar action. This only installs Mathlib's module structure in the type.
Source: Stacks Project, algebra.tex, Tags 07JZ and 07K0
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
abbrev scalarLocalizationHomEquiv (A : Type v) [CommRing A] (t : A)
    (M : Type w) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module (Localization.Away t) N] :=
  (fun [_localizedModule : Module (Localization.Away t) (LocalizedModule.Away t M)] ↦
    LocalizedModule.Away t M ≃ₗ[Localization.Away t] N)
    (_localizedModule := LocalizedModule.moduleOfIsLocalization
      (S := Submonoid.powers t) (T := Localization.Away t) (M := M))

private theorem localization_isFlat (R : Sheaf J CommRingCat.{u})
    (g : (R.obj ⋙ forget CommRingCat.{u}).sections) :
    SheafOfModules.IsFlat (ringedSectionLocalization R g) := by
  let O := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let F := ringedSectionLocalizationPresheaf R g
  have hflat (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := by
    dsimp [F, ringedSectionLocalizationPresheaf, ringedSectionLocalizationCarrier]
    infer_instance
  have hF : PreservesFiniteLimits (tensorRight F) := by
    constructor
    intro K _ _
    have (V : Cᵒᵖ) : Module.Flat (R.obj.obj V) (F.obj V) := hflat V
    exact ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
      (fun V ↦ isLimitOfPreserves
        (tensorRight (show ModuleCat (R.obj.obj V) from F.obj V))
        (isLimitOfPreserves (PresheafOfModules.evaluation O.obj V) hc))⟩⟩⟩
  have : Presheaf.IsLocallyInjective J (𝟙 O.obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ ↦ Function.injective_id)
  have : Presheaf.IsLocallySurjective J (𝟙 O.obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ ↦ Function.surjective_id)
  exact (PresheafOfModules.isFlat_sheafification_obj (R := R) (𝟙 O.obj) F hF).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full localized-Hom comparison: linear equivalences on all fractions,
contravariant/covariant naturality, identity, composition and simultaneous shift.
The predicates P and B specify respectively the allowed sources and targets;
the theorem below substitutes the actual continuity and lower-bound predicates.
Source: Bhatt–Scholze, Lemma 6.8.12 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-derived-hom). -/
def scalarLocalizationHomComparison (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{w} D] [Preadditive D] [HasShift D ℤ] [Linear A D]
    {T : Type y} [Category.{w} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T] (F : D ⥤ T) [F.CommShift ℤ]
    (P B : D → Prop) : Prop :=
  ∃ e : ∀ (K : D),
    P K →
    ∀ (L : D),
    B L → ∀ q : ℤ,
      scalarLocalizationHomEquiv A t (K ⟶ L⟦q⟧)
        (F.obj K ⟶ (F.obj L)⟦q⟧),
    (∀ K hK L hL q (f : K ⟶ L⟦q⟧) (n : ℕ),
      (e K hK L hL q).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ n •
          (F.map f ≫ (F.commShiftIso q).hom.app L)) ∧
    (∀ K K' hK hK' L L' hL hL' q (f : K' ⟶ K) (g : L ⟶ L')
      (u : K ⟶ L⟦q⟧) (n : ℕ),
      (e K' hK' L' hL' q).toFun (LocalizedModule.mk (f ≫ u ≫ g⟦q⟧') ⟨t ^ n, ⟨n, rfl⟩⟩) =
        F.map f ≫
          (e K hK L hL q).toFun (LocalizedModule.mk u ⟨t ^ n, ⟨n, rfl⟩⟩) ≫
            (F.map g)⟦q⟧') ∧
    (∀ K hK hL,
      (e K hK K hL 0).toFun
        (LocalizedModule.mk ((shiftFunctorZero _ ℤ).inv.app K) 1) =
          (shiftFunctorZero _ ℤ).inv.app (F.obj K)) ∧
    (∀ K L M hK hL hLc hM p q (f : K ⟶ L⟦q⟧) (g : L ⟶ M⟦p⟧) (n m : ℕ),
      (e K hK M hM (p + q)).toFun
        (LocalizedModule.mk
          (f ≫ g⟦q⟧' ≫ (shiftFunctorAdd _ p q).inv.app M)
          ⟨t ^ (n + m), ⟨n + m, rfl⟩⟩) =
        (e K hK L hL q).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) ≫
          ((e L hLc M hM p).toFun (LocalizedModule.mk g ⟨t ^ m, ⟨m, rfl⟩⟩))⟦q⟧' ≫
            (shiftFunctorAdd _ p q).inv.app (F.obj M)) ∧
    (∀ K hK L hL p q hKq hLq (f : K ⟶ L⟦p⟧) (n : ℕ),
      (e (K⟦q⟧) hKq (L⟦q⟧) hLq p).toFun
        (LocalizedModule.mk
          (f⟦q⟧' ≫ (shiftFunctorComm _ p q).hom.app L) ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (F.commShiftIso q).hom.app K ≫
          ((e K hK L hL p).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩))⟦q⟧' ≫
            (shiftFunctorComm _ p q).hom.app (F.obj L) ≫
              ((F.commShiftIso q).inv.app L)⟦p⟧')

attribute [local semireducible] SheafOfModules.monoidalCategory

attribute [local irreducible] scalarLocalizationCoefficientMap
  ringedLocalizationRing ringedLocalizationRingUnit
private def homShiftZeroEquiv
    {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ] (K M : D) :
    (K ⟶ M⟦(0 : ℤ)⟧) ≃+ (K ⟶ M) where
  toFun f := f ≫ (shiftFunctorZero D ℤ).hom.app M
  invFun f := f ≫ (shiftFunctorZero D ℤ).inv.app M
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp only [Preadditive.add_comp]

private theorem continuous_unshifted
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    (K : DerivedCategory B) (hK : DerivedCategory.CountableBoundedBelowHomContinuous K)
    (L : ℕ → DerivedCategory B) (b : ℤ) (hL : ∀ n, (L n).IsGE b)
    (M : DerivedCategory B) (ι : ∀ n : ℕ, L n ⟶ M)
    (hc : IsColimit (Cofan.mk M ι)) :
    Function.Bijective
      (DirectSum.toAddMonoid (fun n ↦ Preadditive.rightComp K (ι n)) :
        (⨁ n : ℕ, (K ⟶ L n)) →+ (K ⟶ M)) := by
  classical
  let e := DFinsupp.mapRange.addEquiv (fun n ↦ homShiftZeroEquiv K (L n))
  let β := DirectSum.toAddMonoid (fun n ↦ Preadditive.rightComp K (ι n))
  let β₀ := DirectSum.toAddMonoid (fun n ↦
    Preadditive.rightComp K ((ι n)⟦(0 : ℤ)⟧'))
  have h : β.comp e.toAddMonoidHom = (homShiftZeroEquiv K M).toAddMonoidHom.comp β₀ := by
    apply DirectSum.addHom_ext
    intro n f
    simp only [AddMonoidHom.comp_apply]
    change β (DirectSum.map (fun n ↦ (homShiftZeroEquiv K (L n)).toAddMonoidHom)
      (DirectSum.of _ n f)) = _
    rw [DirectSum.map_of]
    simp only [β, β₀, DirectSum.toAddMonoid_of]
    change (f ≫ (shiftFunctorZero _ ℤ).hom.app (L n)) ≫ ι n =
      (f ≫ (ι n)⟦(0 : ℤ)⟧') ≫ (shiftFunctorZero _ ℤ).hom.app M
    simpa only [Category.assoc, Functor.id_map] using
      congrArg (fun g ↦ f ≫ g) ((shiftFunctorZero _ ℤ).hom.naturality (ι n)).symm
  have hh : Function.Bijective (β.comp e.toAddMonoidHom) := by
    rw [h]
    exact (homShiftZeroEquiv K M).bijective.comp (hK L b hL M ι hc 0)
  exact ⟨fun x y hxy ↦ by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    exact congrArg e (hh.injective hxy),
    fun y ↦ by
      obtain ⟨x, hx⟩ := hh.surjective y
      exact ⟨e x, hx⟩⟩

private theorem telescope_hom_colimit
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {T : Type*} [Category.{w} T] [Preadditive T] [HasShift T ℤ]
    (A : Type*) [CommRing A] (t : A) [Linear A (DerivedCategory B)]
    [Linear (Localization.Away t) T]
    (F : DerivedCategory B ⥤ T) [F.Additive] [F.CommShift ℤ]
    (U : T ⥤ DerivedCategory B) [U.Additive] [U.CommShift ℤ] (adj : F ⊣ U)
    (htel : scalarLocalizationTelescopeProperty A t F U adj
      (fun L ↦ ∃ b : ℤ, L.IsGE b))
    (K : DerivedCategory B) (hK : K.CountableBoundedBelowHomContinuous)
    (L : DerivedCategory B) (hL : ∃ b : ℤ, L.IsGE b) :
    let X := Functor.ofSequence (X := fun _ : ℕ ↦ L) (fun _ ↦ t • 𝟙 L)
    ∃ e : ↥(colimit (X ⋙ preadditiveCoyoneda.obj (op K))) ≃+ (F.obj K ⟶ F.obj L),
      ∀ (n : ℕ) (f : K ⟶ L),
        e (colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n f) =
          (IsLocalization.Away.invSelf t : Localization.Away t) ^ n • F.map f := by
  classical
  dsimp only
  let X := Functor.ofSequence (X := fun _ : ℕ ↦ L) (fun _ ↦ t • 𝟙 L)
  obtain ⟨B₀, ι, hc, s, hs, H, g, h, ⟨hT, eH, heH⟩, _, _⟩ := htel L hL
  obtain ⟨b, hb⟩ := hL
  obtain ⟨phi, hphi, hbij⟩ := sequence_relative_hom_telescope K X B₀ ι hc s
    (by simpa only [X, Functor.ofSequence_map_homOfLE_succ] using hs) H g h hT
    (continuous_unshifted K hK (fun _ ↦ L) b (fun _ ↦ hb) B₀ ι hc)
    (hK (fun _ ↦ L) b (fun _ ↦ hb) B₀ ι hc 1)
  let e₀ := AddEquiv.ofBijective phi.hom hbij
  let e₁ : (K ⟶ H) ≃+ (K ⟶ U.obj (F.obj L)) :=
    { toFun := fun f ↦ f ≫ eH.hom
      invFun := fun f ↦ f ≫ eH.inv
      left_inv := by intro f; simp [Category.assoc]
      right_inv := by intro f; simp [Category.assoc]
      map_add' := by intros; simp only [Preadditive.add_comp] }
  let e₂ : (K ⟶ U.obj (F.obj L)) ≃+ (F.obj K ⟶ F.obj L) :=
    (adj.homAddEquiv K (F.obj L)).symm
  refine ⟨e₀.trans (e₁.trans e₂), ?_⟩
  intro n f
  change e₂ (phi (colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n f) ≫ eH.hom) = _
  rw [hphi]
  simp only [Category.assoc]
  change e₂ (f ≫ ι n ≫ g ≫ eH.hom) = _
  rw [heH]
  change (adj.homEquiv K (F.obj L)).symm
    (f ≫ adj.unit.app L ≫ U.map
      (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 (F.obj L))) = _
  have hn : f ≫ adj.unit.app L = adj.unit.app K ≫ U.map (F.map f) :=
    adj.unit.naturality f
  rw [← Category.assoc f, hn]
  simp only [Category.assoc, ← U.map_comp]
  rw [← Adjunction.homEquiv_unit]
  simp only [Equiv.symm_apply_apply, Linear.comp_smul, Category.comp_id]

private theorem hom_colimit_fractions
    {D : Type u} [Category.{w} D] [Preadditive D]
    (A : Type v) [CommRing A] [Linear A D] (t : A) (K L : D) :
    let X := Functor.ofSequence (X := fun _ : ℕ ↦ L) (fun _ ↦ t • 𝟙 L)
    ∃ e : LocalizedModule.Away t (K ⟶ L) ≃+
        ↥(colimit (X ⋙ preadditiveCoyoneda.obj (op K))),
      ∀ (n : ℕ) (f : K ⟶ L),
        e (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
          colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n f := by
  classical
  dsimp only
  let X := Functor.ofSequence (X := fun _ : ℕ ↦ L) (fun _ ↦ t • 𝟙 L)
  let Y : ℕ ⥤ ModuleCat.{w} A :=
    Functor.ofSequence (X := fun _ : ℕ ↦ ModuleCat.of A (K ⟶ L))
      (fun _ ↦ ModuleCat.ofHom (LinearMap.lsmul A (K ⟶ L) t))
  let G := forget₂ (ModuleCat.{w} A) AddCommGrpCat
  let τ : Y ⋙ G ⟶ X ⋙ preadditiveCoyoneda.obj (op K) :=
    NatTrans.ofSequence (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [X, Y, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ]
      ext f
      change t • (show K ⟶ L from f) = f ≫ (t • 𝟙 L)
      simp only [Linear.comp_smul, Category.comp_id])
  let α : Y ⋙ G ≅ X ⋙ preadditiveCoyoneda.obj (op K) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun z ↦ τ.naturality z)
  let β := preservesColimitIso G Y ≪≫ HasColimit.isoOfNatIso α
  obtain ⟨κ, hκ⟩ := ModuleCat.localization_away_colimit t (K ⟶ L)
  let eb : ↥(colimit Y) ≃+ ↥(colimit (X ⋙ preadditiveCoyoneda.obj (op K))) :=
    { toFun := β.hom
      invFun := β.inv
      left_inv := fun f ↦ ConcreteCategory.congr_hom β.hom_inv_id f
      right_inv := fun f ↦ ConcreteCategory.congr_hom β.inv_hom_id f
      map_add' := β.hom.hom.map_add }
  refine ⟨κ.toAddEquiv.symm.trans eb, ?_⟩
  intro n f
  change eb (κ.symm (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩)) = _
  rw [← hκ n f, κ.symm_apply_apply]
  change β.hom ((colimit.ι Y n) f) = _
  have h := ι_preservesColimitIso_hom G Y n
  have h' := HasColimit.ι_isoOfNatIso_hom α n
  have hh : G.map (colimit.ι Y n) ≫ β.hom =
      α.hom.app n ≫ colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n := by
    calc
      G.map (colimit.ι Y n) ≫ β.hom =
          colimit.ι (Y ⋙ G) n ≫ (HasColimit.isoOfNatIso α).hom := by
        dsimp only [β, Iso.trans_hom]
        rw [← Category.assoc, h]
      _ = α.hom.app n ≫ colimit.ι (X ⋙ preadditiveCoyoneda.obj (op K)) n := h'
  exact ConcreteCategory.congr_hom hh f

set_option backward.isDefEq.respectTransparency false in
private theorem fraction_addEquiv_linear
    (A : Type u) [CommRing A] (t : A)
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module (Localization.Away t) N]
    (e : LocalizedModule.Away t M ≃+ N)
    (f : M → N)
    (hf : ∀ (r : A) (m : M), f (r • m) = algebraMap A (Localization.Away t) r • f m)
    (he : ∀ (m : M) (n : ℕ),
      e (LocalizedModule.mk m ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ n • f m) :
    ∃ E : (fun [_localized : Module (Localization.Away t) (LocalizedModule.Away t M)] ↦
      LocalizedModule.Away t M ≃ₗ[Localization.Away t] N)
      (_localized := LocalizedModule.moduleOfIsLocalization
        (S := Submonoid.powers t) (T := Localization.Away t) (M := M)),
      ∀ x, E x = e x := by
  let : Module (Localization.Away t) (LocalizedModule.Away t M) :=
    LocalizedModule.moduleOfIsLocalization
      (S := Submonoid.powers t) (T := Localization.Away t) (M := M)
  let : Module A N := Module.compHom N (algebraMap A (Localization.Away t))
  have : IsScalarTower A (Localization.Away t) N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  let E : LocalizedModule.Away t M ≃ₗ[A] N :=
    { toAddEquiv := e
      map_smul' := by
        intro r x
        induction x using LocalizedModule.induction_on with
        | _ m s =>
          obtain ⟨n, hn⟩ := s.property
          have hs : s = ⟨t ^ n, ⟨n, rfl⟩⟩ := Subtype.ext hn.symm
          subst s
          rw [LocalizedModule.smul'_mk]
          change e (LocalizedModule.mk (r • m) ⟨t ^ n, ⟨n, rfl⟩⟩) =
            algebraMap A (Localization.Away t) r •
              e (LocalizedModule.mk m ⟨t ^ n, ⟨n, rfl⟩⟩)
          rw [he, he, hf]
          exact smul_comm _ _ _ }
  exact ⟨E.extendScalarsOfIsLocalization (Submonoid.powers t) (Localization.Away t),
    fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarHomComparison_of_normalized (A : Type v) [CommRing A] (t : A)
    {D : Type x} [Category.{w} D] [Preadditive D] [HasShift D ℤ] [Linear A D]
    {T : Type y} [Category.{w} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T] (F : D ⥤ T) [F.CommShift ℤ]
    (P B : D → Prop)
    [∀ q : ℤ, (shiftFunctor T q).Linear (Localization.Away t)]
    (hnorm : ∃ e : ∀ (K : D),
    P K →
    ∀ (L : D),
    B L → ∀ q : ℤ,
      scalarLocalizationHomEquiv A t (K ⟶ L⟦q⟧)
        (F.obj K ⟶ (F.obj L)⟦q⟧),
    (∀ K hK L hL q (f : K ⟶ L⟦q⟧) (n : ℕ),
      (e K hK L hL q).toFun (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
        (IsLocalization.Away.invSelf t : Localization.Away t) ^ n •
          (F.map f ≫ (F.commShiftIso q).hom.app L))) :
    scalarLocalizationHomComparison A t F P B := by
  obtain ⟨e, he⟩ := hnorm
  refine ⟨e, he, ?_, ?_, ?_, ?_⟩
  · intro K K' hK hK' L L' hL hL' q f g z n
    rw [he, he]
    simp only [Functor.map_comp, Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [F.commShiftIso_hom_naturality]
  · intro K hK hL
    have hn := he K hK K hL 0 ((shiftFunctorZero _ ℤ).inv.app K) 0
    simp only [pow_zero, one_smul] at hn
    have hden : (1 : Submonoid.powers t) = ⟨(1 : A), by simp⟩ := rfl
    rw [hden, hn, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.id_obj]
    rw [F.map_id, Category.id_comp]
  · intro K L M hK hL hLc hM p q f g n m
    rw [he, he, he]
    simp only [Functor.map_comp, Functor.map_smul, Functor.map_comp,
      Linear.smul_comp, Linear.comp_smul, smul_smul, pow_add, Category.assoc]
    congr 1
    · exact mul_comm _ _
    rw [F.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    simp only [← F.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id, Functor.map_comp, Category.assoc,
      F.commShiftIso_hom_naturality_assoc]
  · intro K hK L hL p q hKq hLq f n
    rw [he, he]
    simp only [Functor.map_comp, F.map_shiftFunctorComm_hom_app,
      Functor.map_smul, Linear.smul_comp, Linear.comp_smul, Category.assoc,
      Iso.inv_hom_id_app]
    congr 1
    dsimp only [Functor.comp_obj]
    simp only [Category.comp_id]
    rw [F.commShiftIso_hom_naturality_assoc]

private theorem hom_comparison_of_telescope
    {B : Type u} [Category.{v} B] [Abelian B] [HasDerivedCategory.{w} B]
    {T : Type y} [Category.{w} T] [Preadditive T] [HasShift T ℤ]
    (A : Type x) [CommRing A] (t : A) [Linear A (DerivedCategory B)]
    [Linear (Localization.Away t) T]
    [∀ q : ℤ, (shiftFunctor T q).Linear (Localization.Away t)]
    (F : DerivedCategory B ⥤ T) [F.Additive] [F.CommShift ℤ]
    (U : T ⥤ DerivedCategory B) [U.Additive] [U.CommShift ℤ] (adj : F ⊣ U)
    (hsemi : ∀ {K L : DerivedCategory B} (f : K ⟶ L) (r : A),
      F.map (r • f) = algebraMap A (Localization.Away t) r • F.map f)
    (htel : scalarLocalizationTelescopeProperty A t F U adj
      (fun L ↦ ∃ b : ℤ, L.IsGE b)) :
    scalarLocalizationHomComparison A t F DerivedCategory.CountableBoundedBelowHomContinuous
      (fun L ↦ ∃ b : ℤ, L.IsGE b) := by
  classical
  apply scalarHomComparison_of_normalized
  have hh : ∀ (K : DerivedCategory B), K.CountableBoundedBelowHomContinuous →
      ∀ (L : DerivedCategory B), (∃ b : ℤ, L.IsGE b) → ∀ q : ℤ,
        ∃ e : scalarLocalizationHomEquiv A t (K ⟶ L⟦q⟧) (F.obj K ⟶ (F.obj L)⟦q⟧),
          ∀ (f : K ⟶ L⟦q⟧) (n : ℕ),
            e (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
              (IsLocalization.Away.invSelf t : Localization.Away t) ^ n •
                (F.map f ≫ (F.commShiftIso q).hom.app L) := by
    intro K hK L hL q
    obtain ⟨b, hb⟩ := hL
    have hLq : ∃ b : ℤ, (L⟦q⟧).IsGE b := by
      let := hb
      exact ⟨b - q, DerivedCategory.TStructure.t.isGE_shift L b q (b - q) (by omega)⟩
    obtain ⟨e₁, he₁⟩ := hom_colimit_fractions A t K (L⟦q⟧)
    obtain ⟨e₂, he₂⟩ := telescope_hom_colimit A t F U adj htel K hK (L⟦q⟧) hLq
    let ec : (F.obj K ⟶ F.obj (L⟦q⟧)) ≃+ (F.obj K ⟶ (F.obj L)⟦q⟧) :=
      { toFun := fun f ↦ f ≫ (F.commShiftIso q).hom.app L
        invFun := fun f ↦ f ≫ (F.commShiftIso q).inv.app L
        left_inv := by intro f; simp [Category.assoc]
        right_inv := by intro f; simp [Category.assoc]
        map_add' := by intros; simp only [Preadditive.add_comp] }
    let e := e₁.trans (e₂.trans ec)
    have he (f : K ⟶ L⟦q⟧) (n : ℕ) :
        e (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩) =
          (IsLocalization.Away.invSelf t : Localization.Away t) ^ n •
            (F.map f ≫ (F.commShiftIso q).hom.app L) := by
      change ec (e₂ (e₁ (LocalizedModule.mk f ⟨t ^ n, ⟨n, rfl⟩⟩))) = _
      rw [he₁, he₂]
      exact Linear.smul_comp _ _ _ _ _ _
    obtain ⟨E, hE⟩ := fraction_addEquiv_linear A t (K ⟶ L⟦q⟧)
      (F.obj K ⟶ (F.obj L)⟦q⟧) e
      (fun f ↦ F.map f ≫ (F.commShiftIso q).hom.app L)
      (by intro r f; rw [hsemi]; exact Linear.smul_comp _ _ _ _ _ _)
      he
    exact ⟨E, fun f n ↦ (hE _).trans (he f n)⟩
  choose e he using hh
  exact ⟨e, he⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_adjunction_descends
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {T : Type uT} [Category.{vT} T] [Abelian T] [HasDerivedCategory.{w} T]
    (E : B ⥤ T) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : T ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : E ⊣ U) :
    ∃ d : E.mapDerivedCategory ⊣ U.mapDerivedCategory,
      scalarLocalizationTelescopeDerivedUnit E U
        (fun K ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K) d := by
  let EC := E.mapHomologicalComplex (.up ℤ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let : CatCommSq EC DerivedCategory.Q DerivedCategory.Q E.mapDerivedCategory :=
    ⟨E.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq UC DerivedCategory.Q DerivedCategory.Q U.mapDerivedCategory :=
    ⟨U.mapDerivedCategoryFactors.symm⟩
  let d := (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso B (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso T (.up ℤ))
    E.mapDerivedCategory U.mapDerivedCategory
  refine ⟨d, ?_⟩
  intro K
  dsimp only [d]
  rw [Adjunction.localization_unit_app]
  simp only [Category.assoc]
  change DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
    U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
    U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app K) ≫
    U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
    U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) = _
  have hiE := E.mapDerivedCategoryFactors.inv_hom_id_app K
  have hiU := U.mapDerivedCategoryFactors.inv_hom_id_app
    ((E.mapHomologicalComplex (.up ℤ)).obj K)
  have hh := congrArg U.mapDerivedCategory.map hiE
  rw [Functor.map_comp, Functor.map_id] at hh
  calc
    _ = DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        U.mapDerivedCategoryFactors.inv.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.inv.app K) ≫
        U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K)) ≫
        U.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [hh]
      dsimp only [Functor.comp_obj] at hiU ⊢
      rw [Category.id_comp, hiU, Category.comp_id]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 100000 in
-- Match the coefficient actions through the sheaf restriction functor.
private theorem restrict_scalar_identity
    (A : Type v) [CommRing A] (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (ringedLocalizationRing R (a t)))) (r : A) :
    (fun [_src : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_tgt : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRing R (a t))))] ↦
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          (ringedLocalizationRingUnit R (a t)))).map
            (algebraMap A (Localization.Away t) r • 𝟙 N) =
        r • 𝟙 ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map
            (ringedLocalizationRingUnit R (a t)))).obj N))
      (_src := scalarLocalizationCoefficientLinear A R a)
      (_tgt := scalarLocalizationCoefficientLinear (Localization.Away t)
        (ringedLocalizationRing R (a t)) (scalarLocalizationCoefficientMap A R a t)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (scalarLocalizationCoefficientMap A R a t
    (algebraMap A (Localization.Away t) r)).val V •
      (show N.val.obj V from x) = (a r).val V • x
  have h : scalarLocalizationCoefficientMap A R a t
      (algebraMap A (Localization.Away t) r) =
      scalarLocalizationSectionsMap (ringedLocalizationRingUnit R (a t)) (a r) := by
    unfold scalarLocalizationCoefficientMap
    exact IsLocalization.Away.lift_eq (S := Localization.Away t) t
      (scalarLocalizationSections_isUnit A R a t) r
  exact congrArg (fun z ↦ z.val V • (show N.val.obj V from x)) h

private theorem left_adjoint_semilinear
    {B T : Type*} [Category B] [Category T] [Preadditive B] [Preadditive T]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A B] [Linear S T]
    (φ : A →+* S) (E : B ⥤ T) (U : T ⥤ B) (adj : E ⊣ U)
    (hU : ∀ (N : T) (r : A), U.map (φ r • 𝟙 N) = r • 𝟙 (U.obj N))
    (M : B) (r : A) : E.map (r • 𝟙 M) = φ r • 𝟙 (E.obj M) := by
  apply (adj.homEquiv M (E.obj M)).injective
  simp only [Adjunction.homEquiv_unit, hU]
  have hn : (r • 𝟙 M) ≫ adj.unit.app M =
      adj.unit.app M ≫ U.map (E.map (r • 𝟙 M)) := adj.unit.naturality _
  rw [← hn]
  dsimp only [Functor.comp_obj]
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_derived_semilinear
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory.{w} B]
    {T : Type*} [Category T] [Abelian T] [HasDerivedCategory.{w} T]
    {A S : Type*} [CommRing A] [CommRing S] [Linear A B] [Linear S T]
    (φ : A →+* S)
    (E : B ⥤ T) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (hE : ∀ (M : B) (r : A), E.map (r • 𝟙 M) = φ r • 𝟙 (E.obj M)) :
    ∀ {K L : DerivedCategory B} (f : K ⟶ L) (r : A),
      E.mapDerivedCategory.map (r • f) = φ r • E.mapDerivedCategory.map f := by
  have hQ (P : CochainComplex B ℤ) (r : A) :
      E.mapDerivedCategory.map (r • 𝟙 (DerivedCategory.Q.obj P)) =
        φ r • 𝟙 (E.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    have hcomplex : (E.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 P) =
        φ r • 𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj P) := by
      apply HomologicalComplex.hom_ext
      intro i
      exact hE (P.X i) r
    have hQmap : DerivedCategory.Q.map (r • 𝟙 P) =
        r • 𝟙 (DerivedCategory.Q.obj P) := by
      rw [Functor.map_smul, Functor.map_id]
    rw [← hQmap]
    apply (cancel_mono (E.mapDerivedCategoryFactors.hom.app P)).1
    have hn := E.mapDerivedCategoryFactors.hom.naturality (r • 𝟙 P)
    change E.mapDerivedCategory.map (DerivedCategory.Q.map (r • 𝟙 P)) ≫
        E.mapDerivedCategoryFactors.hom.app P =
      E.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((E.mapHomologicalComplex (.up ℤ)).map (r • 𝟙 P)) at hn
    rw [hn, hcomplex, Functor.map_smul, Functor.map_id]
    dsimp only [Functor.comp_obj]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  have hid (K : DerivedCategory B) (r : A) :
      E.mapDerivedCategory.map (r • 𝟙 K) = φ r • 𝟙 (E.mapDerivedCategory.obj K) := by
    let P := DerivedCategory.Q.objPreimage K
    let e := DerivedCategory.Q.objObjPreimageIso K
    have hh : r • 𝟙 K = e.inv ≫ (r • 𝟙 (DerivedCategory.Q.obj P)) ≫ e.hom := by
      dsimp only [P]
      simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, Iso.inv_hom_id]
    rw [hh, Functor.map_comp, Functor.map_comp, hQ]
    dsimp only [P]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id]
  intro K L f r
  have hh : r • f = (r • 𝟙 K) ≫ f := by
    simp only [Linear.smul_comp, Category.id_comp]
  rw [hh, Functor.map_comp, hid]
  simp only [Linear.smul_comp, Category.id_comp]

end CategoryTheory
