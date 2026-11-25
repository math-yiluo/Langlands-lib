/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DeligneLaumon.RationalContinuousCoefficientDerivedLocalization
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnderlyingTelescope
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact

import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationFractionColimitOfUniverses
import WeilConjectures.Algebra.Homology.Scalar.ScalarLocalizationCoefficientAdjunctionOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationTelescopeLaws
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnitShift
import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationUnitFactors

/-! # Localization telescopes with independent site universes

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2); Stacks Tags 093W and 0949.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe uC vC u v w uD vD uT vT uB vB r a b
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Opposite
open scoped ChangeOfRings
open CategoryTheory.Pretriangulated
namespace CategoryTheory
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

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
private theorem restrict_scalar_identity
    (A : Type v) [CommRing A] (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    (N : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
      (ringedLocalizationRingOfUniverses R (a t)))) (r : A) :
    (fun [_src : Linear A (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
      [_tgt : Linear (Localization.Away t) (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R (a t))))] ↦
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map
          (ringedLocalizationRingUnitOfUniverses R (a t)))).map
            (algebraMap A (Localization.Away t) r • 𝟙 N) =
        r • 𝟙 ((SheafOfModules.restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).map
            (ringedLocalizationRingUnitOfUniverses R (a t)))).obj N))
      (_src := scalarLocalizationCoefficientLinearOfUniverses A R a)
      (_tgt := scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
        (ringedLocalizationRingOfUniverses R (a t)) (scalarLocalizationCoefficientMapOfUniverses A
          R a t)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (scalarLocalizationCoefficientMapOfUniverses A R a t
    (algebraMap A (Localization.Away t) r)).val V •
      (show N.val.obj V from x) = (a r).val V • x
  have h : scalarLocalizationCoefficientMapOfUniverses A R a t
      (algebraMap A (Localization.Away t) r) =
      scalarLocalizationSectionsMapOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t)) (a
        r) := by
    unfold scalarLocalizationCoefficientMapOfUniverses
    exact IsLocalization.Away.lift_eq (S := Localization.Away t) t
      (scalarLocalizationSections_isUnitOfUniverses A R a t) r
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

namespace CategoryTheory
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- Restriction of localized coefficients is the normalized scalar telescope.
The statement has independent object, morphism and coefficient universes and makes no
assertion about Hom groups or Hom continuity.

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14(2), pp. 61--62;
Stacks Tags 093W, 0949 and 015F; the universe-independent form of
lem-weil-pbc-scalar-localization-underlying-telescope.
(blueprint: lem-weil-pbc-scalar-localization-telescope-of-universes).

Proof: take ordinary restriction along the sheaf localization unit. It is additive and
exact, and tensor extension is its left adjoint, with unit m mapped to 1 tensor m.
Descend this exact adjunction through the quasi-isomorphism localizations of complexes.
On each module, restriction of localization is the filtered colimit of multiplication
by t. Sectionwise localization fractions identify the colimit maps with t^(-n) times
the unit; sheafification preserves this filtered colimit. Apply this degreewise to a
bounded-below complex. Exact filtered colimits compute the derived colimit, so its
mapping telescope is the cone of identity minus successor on the countable direct sum.
The resulting triangle is distinguished. Its comparison with restricted localization
has precisely the displayed legs. The unit is natural, and its termwise tensor formula
commutes with every shift; descent gives the naturality and shift laws in the telescope
predicate. The scalar equation follows first on identity morphisms from tensor balancing,
then on every map by composition, and then descends through the derived localization.
The tensor comparison and fraction colimit are constructed directly with independent
site universes. Coefficient-universe Grothendieck instances provide the exact filtered
colimits and countable coproducts used by the complex-colimit theorem. No
invertibility or regularity of t in the original ring is used; t=0 gives zero localization.
The empty site and zero modules are included. -/
theorem scalarLocalization_telescopeOfUniverses
    (A : Type v) [CommRing A] (R : Sheaf J CommRingCat.{u})
    (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)) (t : A)
    [HasDerivedCategory.{w}
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))]
    (F : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
        (ringedLocalizationRingOfUniverses R (a t))))
    (hF : ∀ M, F.obj M =
      SheafOfModules.changeOfRingsOfUniverses (ringedLocalizationRingUnitOfUniverses R (a t)) M)
    (_hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hF M) ≫
      SheafOfModules.changeOfRingsHomOfUniverses
        (ringedLocalizationRingUnitOfUniverses R (a t)) M f ≫ eqToHom (hF N).symm)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    letI := scalarLocalizationDerivedLinearOfUniverses A R a
    letI := scalarLocalizationDerivedLinearOfUniverses (Localization.Away t)
      (ringedLocalizationRingOfUniverses R (a t))
      (scalarLocalizationCoefficientMapOfUniverses A R a t)
    ∃ (U : DerivedCategory (ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
          (ringedLocalizationRingOfUniverses R (a t)))) ⥤
        DerivedCategory (ringedSiteModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
      (_add : U.Additive) (_shift : U.CommShift ℤ) (adj : F.mapDerivedCategory ⊣ U),
      scalarLocalizationTelescopeProperty A t F.mapDerivedCategory U adj
        (fun L ↦ ∃ b : ℤ, L.IsGE b) ∧
      (∀ {K L} (f : K ⟶ L) (r : A),
        F.mapDerivedCategory.map (r • f) =
          algebraMap A (Localization.Away t) r • F.mapDerivedCategory.map f)  := by
  classical
  let φ := ringedLocalizationRingUnitOfUniverses R (a t)
  let U := SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  -- Share the witnesses and their specifications without repeatedly reducing the
  -- large dependent goal when eliminating the existential statements.
  have hU :=
    SheafOfModules.scalarLocalizationCoefficientAdjunctionOfUniverses φ
  have : PreservesFiniteLimits U := hU.choose
  have : PreservesFiniteColimits U := hU.choose_spec.choose
  have hadj := hU.choose_spec.choose_spec F hF _hmap
  let adj := hadj.choose
  have hnorm := hadj.choose_spec
  have hderived := exact_adjunction_descends F U adj
  let d := hderived.choose
  have hd := hderived.choose_spec
  let η := fun K ↦ (adj.mapHomologicalComplex (.up ℤ)).unit.app K
  have hsections : ∀ K i,
      scalarLocalizationUnitSectionsOfUniverses φ (K.X i) (F.obj (K.X i)) (hF (K.X i))
        ((η K).f i ≫ eqToHom (congrArg (fun T ↦ T.obj (F.obj (K.X i)))
          (show U = SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) from rfl))) := by
    intro K i V x
    have h := hnorm (K.X i) (SheafOfModules.changeOfRingsOfUniverses φ (K.X i))
      (𝟙 (SheafOfModules.changeOfRingsOfUniverses φ (K.X i))) V x
    simpa only [Adjunction.homEquiv_unit, eqToHom_refl, Category.comp_id,
      SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.id_apply, η,
      Adjunction.mapHomologicalComplex_unit_app_f] using h
  let B := ringedSiteModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let B' := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj
    (ringedLocalizationRingOfUniverses R (a t)))
  let : Linear A B := scalarLocalizationCoefficientLinearOfUniverses A R a
  let : Linear (Localization.Away t) B' :=
    scalarLocalizationCoefficientLinearOfUniverses (Localization.Away t)
      (ringedLocalizationRingOfUniverses R (a t))
      (scalarLocalizationCoefficientMapOfUniverses A R a t)
  let : Linear A (DerivedCategory B) := scalarLocalizationDerivedLinearOfUniverses A R a
  let : Linear (Localization.Away t) (DerivedCategory B') :=
    scalarLocalizationDerivedLinearOfUniverses (Localization.Away t)
      (ringedLocalizationRingOfUniverses R (a t))
      (scalarLocalizationCoefficientMapOfUniverses A R a t)
  have : IsGrothendieckAbelian.{u} B :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  have : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  have hB : HasColimitsOfSize.{u, u} B := IsGrothendieckAbelian.hasColimits B
  have : HasCoproducts.{u} B := fun J ↦ hB.has_colimits_of_shape (Discrete J)
  have : HasCoproducts.{0} B := hasCoproducts_shrink.{0, u} (C := B)
  have : HasCountableCoproducts B := hasCountableCoproducts_of_hasCoproducts B
  have : AB5OfSize.{0, 0} B := AB5OfSize_shrink.{0, 0, u, u} B
  have : d.CommShift ℤ := scalarLocalization_unit_commShift F U d η hd (by
    intro K k
    apply HomologicalComplex.hom_ext
    intro i
    simp only [Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      CochainComplex.shiftFunctor_map_f']
    change adj.unit.app (K.X (i + k)) ≫ U.map (𝟙 (F.obj (K.X (i + k)))) ≫
      𝟙 (U.obj (F.obj (K.X (i + k)))) = adj.unit.app (K.X (i + k))
    erw [U.map_id, Category.comp_id])
  refine ⟨U.mapDerivedCategory, inferInstance, inferInstance, d, ?_, ?_⟩
  · exact telescope_of_complexColimit A t F U η d hd
      (scalarLocalization_complexColimitOfUniverses A R a t F hF _hmap U rfl η hsections)
      (fun L ↦ ∃ b : ℤ, L.IsGE b)
  · intro K L f r
    exact exact_derived_semilinear (algebraMap A (Localization.Away t)) F
      (fun M r ↦ left_adjoint_semilinear (algebraMap A (Localization.Away t)) F U adj
        (fun N r ↦ restrict_scalar_identity A R a t N r) M r) f r

end CategoryTheory
