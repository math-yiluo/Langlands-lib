/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationCoefficientActions
public import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Ringed.RingedSectionLocalizationRing
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationCoefficientActions
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.ProperBaseChange.ExtensionTensorComparisonSupplement
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationTelescopeLaws
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnitShift
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnitFactors

/-!
# The underlying telescope for scalar localization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), with the telescope
model expanded using Stacks Project, Derived Categories, Lemma 0949 and Lemma 093W
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048

universe u v w uD vD uT vT

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DirectSum
open scoped ChangeOfRings

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The nth scalar-localization leg, for a specified adjunction and scalar action.
The theorem below supplies the canonical derived action and the normalized unit.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2)
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeLeg
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [Linear (Localization.Away t) T]
    (F : D ⥤ T) (U : T ⥤ D) (adj : F ⊣ U) (L : D) (n : ℕ) : L ⟶ U.obj (F.obj L) :=
  adj.unit.app L ≫ U.map
    (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) • 𝟙 (F.obj L))

/-- The derived unit is the class of the specified termwise unit on every complex,
after the canonical exact-functor factorization isomorphisms.
Source: Stacks Project, Derived Categories, Tags 05RU and 015F
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeDerivedUnit
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type uT} [Category.{vT} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U : B' ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (unitComplex : ∀ (K : CochainComplex B ℤ),
      K ⟶ (U.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (adj : E.mapDerivedCategory ⊣ U.mapDerivedCategory) : Prop :=
  ∀ (K : CochainComplex B ℤ),
    adj.unit.app (DerivedCategory.Q.obj K) ≫
      U.mapDerivedCategory.map (E.mapDerivedCategoryFactors.hom.app K) ≫
      U.mapDerivedCategoryFactors.hom.app
        ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      DerivedCategory.Q.map (unitComplex K)

/-- The telescope triangle with all its specified legs, naturality and shift equations.
The predicate P records which source objects need the telescope comparison; the theorem
below substitutes the bounded-below predicate and the canonical derived scalar actions.
Source: Stacks Project, Derived Categories, Tags 093W, 0949 and 014A
(blueprint: lem-weil-pbc-scalar-localization-underlying-telescope). -/
def scalarLocalizationTelescopeProperty
    (A : Type v) [CommRing A] (t : A)
    {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ k : ℤ, (shiftFunctor D k).Additive] [Pretriangulated D] [Linear A D]
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasShift T ℤ]
    [Linear (Localization.Away t) T]
    (F : D ⥤ T) [F.CommShift ℤ] (U : T ⥤ D) [U.CommShift ℤ]
    (adj : F ⊣ U) (P : D → Prop) : Prop :=
  ∀ (L : D), P L →
    ∃ (A₀ : D) (ι : ∀ _n : ℕ, L ⟶ A₀) (_hc : IsColimit (Cofan.mk A₀ ι))
      (s : A₀ ⟶ A₀) (_hs : ∀ n : ℕ, ι n ≫ s = (t • 𝟙 L) ≫ ι (n + 1))
      (H : D) (g : A₀ ⟶ H) (h : H ⟶ A₀⟦(1 : ℤ)⟧),
      (Triangle.mk (𝟙 A₀ - s) g h ∈ distTriang D ∧
        ∃ e : H ≅ U.obj (F.obj L),
          ∀ n : ℕ, ι n ≫ g ≫ e.hom = scalarLocalizationTelescopeLeg A t F U adj L n) ∧
      (∀ (K L : D) (f : K ⟶ L) (n : ℕ),
        f ≫ scalarLocalizationTelescopeLeg A t F U adj L n =
          scalarLocalizationTelescopeLeg A t F U adj K n ≫ U.map (F.map f)) ∧
      (∀ (L : D) (n : ℕ) (k : ℤ),
        scalarLocalizationTelescopeLeg A t F U adj (L⟦k⟧) n ≫
          ((F ⋙ U).commShiftIso k).hom.app L =
        (scalarLocalizationTelescopeLeg A t F U adj L n)⟦k⟧')

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem telescope_of_complexColimit
    (A : Type v) [CommRing A] (t : A)
    {B : Type uD} [Category.{vD} B] [Abelian B] [HasDerivedCategory.{w} B]
    {B' : Type uT} [Category.{vT} B'] [Abelian B'] [HasDerivedCategory.{w} B']
    [Linear A B] [Linear (Localization.Away t) B']
    [HasCountableCoproducts B] [HasFilteredColimitsOfSize.{0, 0} B] [AB5OfSize.{0, 0} B]
    (E : B ⥤ B') [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (U₀ : B' ⥤ B) [U₀.Additive] [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
    (unitComplex : ∀ K : CochainComplex B ℤ,
      K ⟶ (U₀.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K))
    (adj : E.mapDerivedCategory ⊣ U₀.mapDerivedCategory) [adj.CommShift ℤ]
    (derivedUnit : scalarLocalizationTelescopeDerivedUnit E U₀ unitComplex adj)
    (hcol : ∀ K : CochainComplex B ℤ,
      ∃ c : Cocone (Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)),
        Nonempty (IsColimit c) ∧
        ∃ β : c.pt ≅ (U₀.mapHomologicalComplex (.up ℤ)).obj
            ((E.mapHomologicalComplex (.up ℤ)).obj K),
          ∀ n : ℕ, c.ι.app n ≫ β.hom = unitComplex K ≫
            (U₀.mapHomologicalComplex (.up ℤ)).map
              (((IsLocalization.Away.invSelf t : Localization.Away t) ^ n) •
                𝟙 ((E.mapHomologicalComplex (.up ℤ)).obj K)))
    (P : DerivedCategory B → Prop) :
    scalarLocalizationTelescopeProperty A t E.mapDerivedCategory U₀.mapDerivedCategory adj P := by
  classical
  obtain ⟨hnat, hshift⟩ :=
    scalarLocalizationTelescopeLegLaws A t E.mapDerivedCategory U₀.mapDerivedCategory adj
  intro L _hL
  let K : CochainComplex B ℤ := DerivedCategory.Q.objPreimage L
  let eK : DerivedCategory.Q.obj K ≅ L := DerivedCategory.Q.objObjPreimageIso L
  clear_value K eK
  obtain ⟨c, ⟨hc⟩, β, hβ⟩ :=
    hcol K
  let S := Functor.ofSequence (X := fun _n : ℕ ↦ K) (fun _n ↦ t • 𝟙 K)
  let b : Cofan (fun _n : ℕ ↦ K) :=
    HomologicalComplex.coconeOfHasColimitEval (Discrete.functor (fun _n : ℕ ↦ K))
  have hb : IsColimit b := HomologicalComplex.isColimitCoconeOfHasColimitEval _
  clear_value b
  let s : b.pt ⟶ b.pt := hb.desc (Cofan.mk b.pt
    (fun n : ℕ ↦ (t • 𝟙 K) ≫ b.inj (n + 1)))
  have hs (n : ℕ) : b.inj n ≫ s = (t • 𝟙 K) ≫ b.inj (n + 1) := hb.fac _ ⟨n⟩
  let q : b.pt ⟶ c.pt := hb.desc (Cofan.mk c.pt (fun n : ℕ ↦ c.ι.app n))
  have hq (n : ℕ) : b.inj n ≫ q = c.ι.app n := hb.fac _ ⟨n⟩
  clear_value s q
  have hu (n : ℕ) : b.inj n ≫ (𝟙 b.pt - s) =
      b.inj n - (t • 𝟙 K) ≫ b.inj (n + 1) := by
    simp only [Preadditive.comp_sub, Category.comp_id, hs]
  obtain ⟨p, hp, hp', hqi, ⟨hQB⟩, e, he, htri, htri', hrest⟩ :=
    complex_colimit_homotopyColimit S b hb c hc (𝟙 b.pt - s)
      (fun n ↦ by simpa only [S, Functor.ofSequence_map_homOfLE_succ] using hu n) q hq
  let δ : U₀.mapDerivedCategory.obj (E.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≅
      DerivedCategory.Q.obj
        ((U₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    U₀.mapDerivedCategory.mapIso (E.mapDerivedCategoryFactors.app K) ≪≫
      U₀.mapDerivedCategoryFactors.app ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  let eL : DerivedCategory.Q.obj c.pt ≅
      U₀.mapDerivedCategory.obj (E.mapDerivedCategory.obj L) :=
    DerivedCategory.Q.mapIso β ≪≫ δ.symm ≪≫
      (E.mapDerivedCategory ⋙ U₀.mapDerivedCategory).mapIso eK
  have hlegs (n : ℕ) : DerivedCategory.Q.map (c.ι.app n) ≫
      (DerivedCategory.Q.mapIso β ≪≫ δ.symm).hom =
      scalarLocalizationTelescopeLeg A t E.mapDerivedCategory U₀.mapDerivedCategory
        adj (DerivedCategory.Q.obj K) n := by
    apply (cancel_mono δ.hom).1
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Functor.mapIso_hom]
    rw [← Functor.map_comp, hβ, Functor.map_comp]
    have hh := scalarLocalization_unit_factors (Localization.Away t) E U₀ adj K
      (unitComplex K) (derivedUnit K) (IsLocalization.Away.invSelf t ^ n)
    simpa only [scalarLocalizationTelescopeLeg, Functor.map_comp, δ, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc] using hh
  let ι : ∀ _n : ℕ, L ⟶ DerivedCategory.Q.obj b.pt :=
    fun n ↦ eK.inv ≫ DerivedCategory.Q.map (b.inj n)
  have hι : IsColimit (Cofan.mk (DerivedCategory.Q.obj b.pt) ι) := by
    let d : Discrete.functor (fun _n : ℕ ↦ DerivedCategory.Q.obj K) ≅
        Discrete.functor (fun _n : ℕ ↦ L) := Discrete.natIso (fun _n ↦ eK)
    exact (IsColimit.precomposeInvEquiv d _).symm hQB
  have hsQ (n : ℕ) : ι n ≫ DerivedCategory.Q.map s =
      (t • 𝟙 L) ≫ ι (n + 1) := by
    calc
      ι n ≫ DerivedCategory.Q.map s =
          eK.inv ≫ DerivedCategory.Q.map (b.inj n ≫ s) := by
        simp only [ι, Functor.map_comp, Category.assoc]
      _ = eK.inv ≫ DerivedCategory.Q.map ((t • 𝟙 K) ≫ b.inj (n + 1)) := by rw [hs]
      _ = (t • 𝟙 L) ≫ ι (n + 1) := by
        simp only [ι, Functor.map_smul, Linear.comp_smul, Linear.smul_comp,
          Category.id_comp]
  refine ⟨DerivedCategory.Q.obj b.pt, ι, hι, DerivedCategory.Q.map s, hsQ,
    DerivedCategory.Q.obj c.pt, DerivedCategory.Q.map q,
    e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (𝟙 b.pt - s))).mor₃, ?_, hnat, hshift⟩
  constructor
  · simpa only [Functor.map_sub, Functor.map_id] using htri'
  · refine ⟨eL, ?_⟩
    intro n
    dsimp only [ι, eL, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, ← Functor.map_comp_assoc, hq]
    calc
      _ = eK.inv ≫ scalarLocalizationTelescopeLeg A t E.mapDerivedCategory
          U₀.mapDerivedCategory adj (DerivedCategory.Q.obj K) n ≫
            U₀.mapDerivedCategory.map (E.mapDerivedCategory.map eK.hom) := by
        simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Category.assoc]
          using congrArg (fun f ↦ eK.inv ≫ f ≫
            U₀.mapDerivedCategory.map (E.mapDerivedCategory.map eK.hom)) (hlegs n)
      _ = _ := by
        have hn := congrArg (fun f ↦ eK.inv ≫ f) (hnat _ _ eK.hom n)
        simpa only [scalarLocalizationTelescopeLeg, ← Category.assoc, eK.inv_hom_id,
          Category.id_comp] using hn.symm

end CategoryTheory
