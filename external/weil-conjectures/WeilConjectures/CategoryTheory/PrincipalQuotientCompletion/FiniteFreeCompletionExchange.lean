/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.FiniteFreeQuotientRoosComparison
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
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
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionExists
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Finite free scalar extension and strict quotient completion

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941;
the finite-free and arithmetic comparison extracted in the DAG proof.
(blueprint: lem-pur-finite-free-completion-exchange).

The comparison is specified on K-flat representatives by its two product coordinates.
No basis occurs in its specification.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS a b va vb
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory.PrincipalQuotientCompletion

attribute [local irreducible] quotientTower roosF SheafOfModules.monoidalCategory

/-- The two coordinates of scalar extension of the actual Roos cone, formed from
its product comparison. This uses only the given functor and canonical cone projections.
Source: Stacks 0941, additive cone comparison in DAG proof step 4
(blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable def scalarRoosCoordinates
    {A : Type a} [Category.{va} A] [Abelian A] [HasCountableProducts A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (c : (E.mapHomologicalComplex (.up ℤ)).obj (roosP X) ⟶ roosP Y) (p : ℤ) :
    E.obj ((roosF.obj X).X (p + 1)) ⟶ (roosP Y).X p ⊞ (roosP Y).X (p + 1) :=
  biprod.lift
    (E.map ((roosχ X p).hom ≫ biprod.fst) ≫ c.f p)
    (E.map ((roosχ X p).hom ≫ biprod.snd) ≫ c.f (p + 1))

-- One-variable descent follows from the recorded two-variable descent by
-- holding the second variable fixed at an object in the resolving category.
private theorem singleVariableDescent
    {A D H : Type*} [Category A] [Category D] [Category H]
    (q : A ⥤ D) (a₀ : A)
    (h : ∀ U V : D × D ⥤ H, Function.Bijective
      (fun τ : U ⟶ V ↦ Functor.whiskerLeft (q.prod q) τ))
    (U V : D ⥤ H) : Function.Bijective
      (fun τ : U ⟶ V ↦ Functor.whiskerLeft q τ) := by
  constructor
  · intro τ υ heq
    have hh : Functor.whiskerLeft (q.prod q)
        (Functor.whiskerLeft (Prod.fst D D) τ) =
      Functor.whiskerLeft (q.prod q) (Functor.whiskerLeft (Prod.fst D D) υ) := by
      ext X
      exact NatTrans.congr_app heq X.1
    have hh' := (h (Prod.fst D D ⋙ U) (Prod.fst D D ⋙ V)).1 hh
    ext X
    exact NatTrans.congr_app hh' (X, q.obj a₀)
  · intro τ
    let τ₂ : (q.prod q) ⋙ Prod.fst D D ⋙ U ⟶
        (q.prod q) ⋙ Prod.fst D D ⋙ V :=
      { app := fun X ↦ τ.app X.1
        naturality := fun _ _ f ↦ τ.naturality f.1 }
    obtain ⟨υ, hυ⟩ := (h (Prod.fst D D ⋙ U) (Prod.fst D D ⋙ V)).2 τ₂
    let σ : U ⟶ V :=
      { app := fun X ↦ υ.app (X, q.obj a₀)
        naturality := by
          intro X Y f
          exact υ.naturality (X := (X, q.obj a₀))
            (Y := (Y, q.obj a₀)) (f, 𝟙 (q.obj a₀)) }
    refine ⟨σ, ?_⟩
    ext X
    exact NatTrans.congr_app hυ (X, a₀)

private theorem matrix_zero
    {A : Type u} [Category.{a} A] [Preadditive A] [HasBinaryBiproducts A]
    {B : Type v} [Category.{b} B] [Preadditive B] [HasBinaryBiproducts B]
    (E : A ⥤ B) [E.Additive]
    {P X X₀ X₁ : A} {Y₀ Y₁ Z₀ Z₁ : B}
    (ν : P ⟶ X) (χ : X ⟶ X₀ ⊞ X₁) (q : P ⟶ X₁)
    (hν : ν ≫ χ = biprod.lift 0 q)
    (q' : E.obj P ⟶ Y₁) (c₀ : E.obj X₀ ⟶ Z₀) (c₁ : E.obj X₁ ⟶ Z₁)
    (b : Y₀ ⟶ Z₀) (s : Y₁ ⟶ Z₁) (hq : E.map q ≫ c₁ = q' ≫ s) :
    E.map ν ≫ biprod.lift (E.map (χ ≫ biprod.fst) ≫ c₀)
        (E.map (χ ≫ biprod.snd) ≫ c₁) =
      biprod.lift (0 : E.obj P ⟶ Y₀) q' ≫ biprod.map b s := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc, zero_comp]
    rw [← Category.assoc, ← E.map_comp, ← Category.assoc, hν,
      biprod.lift_fst, E.map_zero, zero_comp]
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    rw [← Category.assoc, ← E.map_comp, ← Category.assoc, hν, biprod.lift_snd]
    exact hq

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]

/-- Termwise application of the recorded ordinary scalar extension.
Source: Stacks 06YT (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev extendedComplex (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ) :=
  F.E.mapHomologicalComplex (.up ℤ)

/-- The source quotient tower of a representative.
Source: Stacks 0941 (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev sourceTower
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  (quotientTower R t).obj P

/-- The target quotient tower, before arithmetic restriction.
Source: Stacks 0941 (blueprint: lem-pur-finite-free-completion-exchange). -/
noncomputable abbrev targetTower (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :=
  (quotientTower S vS).obj ((extendedComplex F).obj P)

/-- The actual Roos comparison data for scalar extension and arithmetic restriction.
Product projections and the two signed cone coordinates specify all maps without a basis.
Source: Stacks 0941 and 0H9K, DAG proof steps 3--6
(blueprint: lem-pur-finite-free-completion-exchange). -/
structure RepresentativeRoosComparison
    {A : Type a} [Category.{va} A] [Abelian A] [HasCountableProducts A]
    {B : Type b} [Category.{vb} B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (e : ℕ) where
  /-- The balanced finite-stage isomorphisms, as one strict tower isomorphism. -/
  β : X.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ index e ⋙ Y.asFunctor
  /-- The canonical tensor/product comparison after the quotient identifications. -/
  c : (E.mapHomologicalComplex (.up ℤ)).obj (roosP X) ⟶
    roosP ((complexRestriction B e).obj Y)
  /-- Every product projection is prescribed. -/
  product_formula : ∀ n : ℕ,
    c ≫ Pi.π _ n =
      (E.mapHomologicalComplex (.up ℤ)).map
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n) ≫ β.hom.app (op n)
  /-- The comparison of actual signed Roos cones. -/
  δ : (E.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅
    roosF.obj ((complexRestriction B e).obj Y)
  /-- Both coordinates are induced by that same product map. -/
  cone_formula : ∀ p : ℤ,
    δ.hom.f (p + 1) ≫ (roosχ ((complexRestriction B e).obj Y) p).hom =
      scalarRoosCoordinates E X ((complexRestriction B e).obj Y) c p
  /-- The arithmetic comparison before localization. -/
  a : roosF.obj Y ⟶ roosF.obj ((complexRestriction B e).obj Y)
  /-- The arithmetic comparison becomes invertible after localization. -/
  arithmetic_quasiIso : QuasiIso a
  /-- The block sum and selection prescribe both arithmetic coordinates. -/
  arithmetic_formula : ∀ p : ℤ,
    a.f (p + 1) ≫ (roosχ ((complexRestriction B e).obj Y) p).hom =
      (roosχ Y p).hom ≫
        biprod.map ((block e Y.asFunctor).f p) ((selection e Y.asFunctor).f (p + 1))

/-- The prescribed representative formula for the completion exchange.
The quotient maps are degreewise epimorphisms, so their equation pins the balanced
finite-stage formula. The final equation specifies inverse arithmetic restriction
following the canonical tensor/product comparison, using the fixed cochain counits.
Source: Stacks 06YT, 0941 and 0H9K, DAG proof steps 3--6
(blueprint: lem-pur-finite-free-completion-exchange). -/
def RepresentativeComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (e : ℕ) (CR : Model R t) (CS : Model S vS)
    (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion)
    (P : CochainComplex
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    :=
  { roos : RepresentativeRoosComparison F.E (sourceTower t P) (targetTower F vS P) e //
    (∀ n : ℕ,
    (extendedComplex F).map (quotientMap R t P n) ≫
        roos.β.hom.app (op n) =
      quotientMap S vS ((extendedComplex F).obj P) (e * (n + 1) - 1)) ∧
    ε.hom.app (DerivedCategory.Q.obj P) ≫
      CS.completion.map (F.ε.app P) ≫ CS.counit.app ((extendedComplex F).obj P) ≫
        DerivedCategory.Q.map roos.a =
      F.T.map (CR.counit.app P) ≫ F.ε.app (roosF.obj (sourceTower t P)) ≫
        DerivedCategory.Q.map roos.δ.hom }

-- Extend an isomorphism given on all K-flat cochain representatives. The
-- two-variable localization theorem supplies descent on the resolving subcategory;
-- a flat resolution then recovers the formula on arbitrary K-flat representatives.
private theorem descendKFlatIso
    {H : Type*} [Category H]
    (U V : DerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ⥤ H)
    (σ : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
      (U.obj (DerivedCategory.Q.obj P) ≅ V.obj (DerivedCategory.Q.obj P)))
    (hσ : ∀ {P P'} (f : P ⟶ P')
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P'),
      U.map (DerivedCategory.Q.map f) ≫ (σ P' hP').hom =
        (σ P hP).hom ≫ V.map (DerivedCategory.Q.map f)) :
    ∃ ε : U ≅ V, ∀ P (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P),
      ε.hom.app (DerivedCategory.Q.obj P) = (σ P hP).hom := by
  classical
  let A := ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)
  obtain ⟨P, hP, _, _, hdesc⟩ :=
    SheafOfModules.site_derived_tensor_descent_independentCoefficients J R
  let q := P.ι ⋙ (DerivedCategory.Qh : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory A)
  obtain ⟨K, _, hK, hflat, _, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R)
      (HomologicalComplex.zero : CochainComplex A ℤ)
  have hKflat : ∀ n, SheafOfModules.IsFlatOnSite (R := R) (K.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (K.X n)).symm (hflat n)
  let a₀ : P.FullSubcategory :=
    ⟨(HomotopyCategory.quotient A (.up ℤ)).obj K, (hP _).2 ⟨hK, hKflat⟩⟩
  have hbij (U' V' : DerivedCategory A ⥤ H) :=
    singleVariableDescent q a₀ (hdesc H inferInstance) U' V'
  let W := (Functor.whiskeringLeft _ _ H).obj q
  let ff : W.FullyFaithful :=
    { preimage := fun {U' V'} τ ↦ ((Equiv.ofBijective _ (hbij U' V')).symm τ)
      map_preimage := fun τ ↦ (Equiv.ofBijective _ (hbij _ _)).apply_symm_apply τ
      preimage_map := fun τ ↦ (Equiv.ofBijective _ (hbij _ _)).symm_apply_apply τ }
  let i := DerivedCategory.quotientCompQhIso A
  let s (X : P.FullSubcategory) : U.obj (q.obj X) ≅ V.obj (q.obj X) :=
    U.mapIso (i.app X.obj.as) ≪≫ σ X.obj.as ((hP _).1 X.property).1 ≪≫
      (V.mapIso (i.app X.obj.as)).symm
  have hs : ∀ (X Y : P.FullSubcategory) (f : X ⟶ Y),
      U.map (q.map f) ≫ (s Y).hom = (s X).hom ≫ V.map (q.map f) := by
    intro X Y f
    have hU := congrArg U.map (i.hom.naturality f.hom.out)
    have hV := congrArg V.map (i.inv.naturality f.hom.out)
    simp only [Functor.comp_map, HomotopyCategory.quotient_map_out,
      Functor.map_comp] at hU hV
    dsimp only [s, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv]
    simp only [q, Functor.comp_map] at ⊢
    calc
      _ = U.map (i.hom.app X.obj.as) ≫
          (U.map (DerivedCategory.Q.map f.hom.out) ≫
            (σ Y.obj.as ((hP _).1 Y.property).1).hom) ≫
              V.map (i.inv.app Y.obj.as) := by
        simpa only [Category.assoc, ObjectProperty.ι_map] using
          congrArg (fun k ↦ k ≫ (σ Y.obj.as ((hP _).1 Y.property).1).hom ≫
            V.map (i.inv.app Y.obj.as)) hU
      _ = U.map (i.hom.app X.obj.as) ≫
          ((σ X.obj.as ((hP _).1 X.property).1).hom ≫
            V.map (DerivedCategory.Q.map f.hom.out)) ≫
              V.map (i.inv.app Y.obj.as) := by
        exact congrArg (fun k ↦ U.map (i.hom.app X.obj.as) ≫ k ≫
          V.map (i.inv.app Y.obj.as))
            (hσ f.hom.out ((hP _).1 X.property).1 ((hP _).1 Y.property).1)
      _ = _ := by
        simpa only [Category.assoc, ObjectProperty.ι_map] using
          congrArg (fun k ↦ U.map (i.hom.app X.obj.as) ≫
            (σ X.obj.as ((hP _).1 X.property).1).hom ≫ k) hV
  let τ : q ⋙ U ≅ q ⋙ V := NatIso.ofComponents s (by
    intro X Y f
    exact hs X Y f)
  let ε := ff.preimageIso τ
  have hε (X : P.FullSubcategory) : ε.hom.app (q.obj X) = (s X).hom :=
    NatTrans.congr_app (ff.map_preimage τ.hom) X
  refine ⟨ε, ?_⟩
  intro L hL
  obtain ⟨K', f, hK', hflat', hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) L
  have hKflat' : ∀ n, SheafOfModules.IsFlatOnSite (R := R) (K'.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (K'.X n)).symm (hflat' n)
  let X : P.FullSubcategory :=
    ⟨(HomotopyCategory.quotient A (.up ℤ)).obj K', (hP _).2 ⟨hK', hKflat'⟩⟩
  have hεK : ε.hom.app (DerivedCategory.Q.obj K') = (σ K' hK').hom := by
    have hn := ε.hom.naturality (i.hom.app K')
    change U.map (i.hom.app K') ≫ ε.hom.app (DerivedCategory.Q.obj K') =
      ε.hom.app (q.obj X) ≫ V.map (i.hom.app K') at hn
    rw [hε X] at hn
    dsimp only [s, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hn
    apply (cancel_epi (U.map (i.hom.app K'))).1
    have hcan : V.map (i.inv.app K') ≫ V.map (i.hom.app K') = 𝟙 _ := by
      rw [← V.map_comp, Iso.inv_hom_id_app, V.map_id]
    change U.map (i.hom.app K') ≫ ε.hom.app (DerivedCategory.Q.obj K') =
      (U.map (i.hom.app K') ≫ (σ K' hK').hom ≫ V.map (i.inv.app K')) ≫
        V.map (i.hom.app K') at hn
    simpa only [Category.assoc, hcan, Category.comp_id] using hn
  let : QuasiIso f := hf
  apply (cancel_epi (U.map (DerivedCategory.Q.map f))).1
  rw [ε.hom.naturality, hεK]
  exact (hσ f hK' hL).symm

private theorem augmentationSquare
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (e : ℕ) (D : QuotientRoosExchange F t vS e) (CR : Model R t) (CS : Model S vS)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    (extendedComplex F).map (CR.augmentation P) ≫ (D.δ P).hom =
      CS.augmentation ((extendedComplex F).obj P) ≫ D.a P := by
  let EC := extendedComplex F
  let Y := (quotientTower S vS).obj (EC.obj P)
  have hprod : EC.map (quotientProduct R t P) ≫ D.c P =
      quotientProduct S vS (EC.obj P) ≫ selection e Y.asFunctor := by
    apply Pi.hom_ext
    intro n
    calc
      _ = EC.map (quotientProduct R t P) ≫
          (EC.map (Pi.π _ n) ≫ (D.β P).hom.app (op n)) := by
        rw [Category.assoc, D.product_formula]
      _ = EC.map (quotientProduct R t P ≫ Pi.π _ n) ≫
          (D.β P).hom.app (op n) := by rw [EC.map_comp, Category.assoc]
      _ = EC.map (quotientMap R t P n) ≫ (D.β P).hom.app (op n) := by
        rw [show quotientProduct R t P ≫ Pi.π _ n = quotientMap R t P n from
          Pi.lift_comp_π _ n]
      _ = quotientMap S vS (EC.obj P) (e * (n + 1) - 1) := D.quotient_formula P n
      _ = quotientProduct S vS (EC.obj P) ≫ Pi.π
          (fun m : ℕ ↦ Y.asFunctor.obj (op m)) (e * (n + 1) - 1) :=
        (Pi.lift_comp_π (quotientMap S vS (EC.obj P)) (e * (n + 1) - 1)).symm
      _ = quotientProduct S vS (EC.obj P) ≫
          (selection e Y.asFunctor ≫ Pi.π
            (fun m : ℕ ↦ Y.asFunctor.obj (op (e * (m + 1) - 1))) n) := by
        exact congrArg (quotientProduct S vS (EC.obj P) ≫ ·)
          (Pi.lift_comp_π (fun m : ℕ ↦ Pi.π
            (fun i : ℕ ↦ Y.asFunctor.obj (op i)) (e * (m + 1) - 1)) n).symm
      _ = _ := (Category.assoc _ _ _).symm
  ext k : 1
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp
  subst k
  apply (cancel_mono (roosχ ((complexRestriction _ e).obj
    ((quotientTower S vS).obj ((extendedComplex F).obj P))) p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [D.cone_formula, D.arithmetic_formula]
  rw [← Category.assoc, CS.coordinates]
  dsimp only [extendedComplex, Functor.mapHomologicalComplex_map_f]
  apply matrix_zero F.E ((CR.augmentation P).f (p + 1))
    (roosχ ((quotientTower R t).obj P) p).hom
    ((quotientProduct R t P).f (p + 1)) (CR.coordinates P p)
    ((quotientProduct S vS ((extendedComplex F).obj P)).f (p + 1))
    ((D.c P).f p) ((D.c P).f (p + 1))
    ((block e ((quotientTower S vS).obj ((extendedComplex F).obj P)).asFunctor).f p)
    ((selection e ((quotientTower S vS).obj
      ((extendedComplex F).obj P)).asFunctor).f (p + 1))
  exact congrArg (fun f ↦ f.f (p + 1)) hprod

private theorem inverse_comparison
    {H : Type*} [Category H] {U V X Y Z : H}
    (ε : U ⟶ V) (α : U ⟶ X) (d : X ⟶ Z) (β : V ⟶ Y) (a : Y ⟶ Z)
    [IsIso β] [IsIso a] (h : ε = (α ≫ d ≫ inv a) ≫ inv β) :
    ε ≫ β ≫ a = α ≫ d := by
  rw [h]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]

private theorem conjugate_natural
    {H : Type*} [Category H] {U U' V V' X X' Y Y' : H}
    (fU : U ⟶ U') (fV : V ⟶ V') (fX : X ⟶ X') (fY : Y ⟶ Y')
    (α : U ⟶ X) (α' : U' ⟶ X') (β : V ⟶ Y) (β' : V' ⟶ Y')
    [IsIso β] [IsIso β'] (θ : X ⟶ Y) (θ' : X' ⟶ Y')
    (hα : fU ≫ α' = α ≫ fX) (hβ : fV ≫ β' = β ≫ fY)
    (hθ : fX ≫ θ' = θ ≫ fY) :
    fU ≫ (α' ≫ θ' ≫ inv β') = (α ≫ θ ≫ inv β) ≫ fV := by
  apply (cancel_mono β').1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hβ, IsIso.inv_hom_id_assoc, reassoc_of% hα, hθ]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem exchangeFromCochains
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (e : ℕ) (D : QuotientRoosExchange F t vS e) (CR : Model R t) (CS : Model S vS) :
    ∃ ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion,
      (∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CS.unit.app (F.T.obj Q)) ∧
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison F t vS e CR CS ε P)) := by
  classical
  let := D.exact_limits
  let := D.exact_colimits
  let := F.universal
  have hεF : IsIso F.ε :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts
      (W := HomologicalComplex.quasiIso _ (.up ℤ)) F.T F.ε (by
        intro P P' f hf
        let : QuasiIso f := hf
        change IsIso (DerivedCategory.Q.map ((F.E.mapHomologicalComplex (.up ℤ)).map f))
        infer_instance)
  let EC := extendedComplex F
  let Z := EC ⋙ quotientTower S vS ⋙ complexRestriction _ e ⋙ roosF ⋙ DerivedCategory.Q
  let d : quotientRoos R t ⋙ EC ⋙ DerivedCategory.Q ≅ Z :=
    NatIso.ofComponents (fun P ↦ DerivedCategory.Q.mapIso (D.δ P)) (by
      intro P P' f
      simpa only [Z, EC, extendedComplex, Functor.comp_map, Functor.map_comp,
        Functor.mapIso_hom] using
        congrArg DerivedCategory.Q.map (D.delta_natural f))
  have ha (P) : IsIso (DerivedCategory.Q.map (D.a P)) := by
    let := D.arithmetic_quasiIso P
    infer_instance
  let a : EC ⋙ quotientRoos S vS ⋙ DerivedCategory.Q ≅ Z :=
    NatIso.ofComponents (fun P ↦ asIso (DerivedCategory.Q.map (D.a P))) (by
      intro P P' f
      simpa only [Z, EC, extendedComplex, Functor.comp_map, Functor.map_comp,
        asIso_hom] using
        congrArg DerivedCategory.Q.map (D.arithmetic_natural f))
  let θ := d ≪≫ a.symm
  let U := CR.completion ⋙ F.T
  let V := F.T ⋙ CS.completion
  let α : DerivedCategory.Q ⋙ U ⟶ quotientRoos R t ⋙ EC ⋙ DerivedCategory.Q :=
    Functor.whiskerRight CR.counit F.T ≫ Functor.whiskerLeft (quotientRoos R t) F.ε
  let β : DerivedCategory.Q ⋙ V ⟶ EC ⋙ quotientRoos S vS ⋙ DerivedCategory.Q :=
    Functor.whiskerRight F.ε CS.completion ≫ Functor.whiskerLeft EC CS.counit
  have hα (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      IsIso (α.app P) := by
    let := CR.computes P hP
    dsimp [α]
    infer_instance
  have hβ (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      IsIso (β.app P) := by
    let := CS.computes (EC.obj P)
      (SheafOfModules.changeOfRings_isKFlat_independentCoefficients φ P
        F.E F.obj_eq F.map_eq hP)
    dsimp [β]
    infer_instance
  let σ (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      U.obj (DerivedCategory.Q.obj P) ≅ V.obj (DerivedCategory.Q.obj P) := by
    let := hα P hP
    let := hβ P hP
    exact asIso (α.app P) ≪≫ θ.app P ≪≫ (asIso (β.app P)).symm
  have hσ : ∀ {P P'} (f : P ⟶ P')
      (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
      (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P'),
      U.map (DerivedCategory.Q.map f) ≫ (σ P' hP').hom =
        (σ P hP).hom ≫ V.map (DerivedCategory.Q.map f) := by
    intro P P' f hP hP'
    let := hβ P hP
    let := hβ P' hP'
    simpa only [σ, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Iso.app_hom, Functor.comp_map, Functor.comp_obj, Category.assoc] using
        conjugate_natural _ _ _ _ _ _ _ _ _ _
          (α.naturality f) (β.naturality f) (θ.hom.naturality f)
  obtain ⟨ε, hε⟩ := descendKFlatIso U V σ hσ
  have hformula (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      ε.hom.app (DerivedCategory.Q.obj P) ≫ β.app P ≫
        DerivedCategory.Q.map (D.a P) = α.app P ≫ DerivedCategory.Q.map (D.δ P).hom := by
    let := hβ P hP
    let := ha P
    apply inverse_comparison
    have hh := hε P hP
    simpa only [σ, θ, d, a, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
      Iso.app_inv, NatTrans.comp_app, asIso_hom, asIso_inv, Functor.mapIso_hom,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      Iso.trans_inv, Category.assoc] using hh
  have hunit (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
      F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫
        ε.hom.app (DerivedCategory.Q.obj P) = CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) := by
    let := hβ P hP
    let := ha P
    have hl : F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫ α.app P =
        F.ε.app P ≫ DerivedCategory.Q.map (EC.map (CR.augmentation P)) := by
      change F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫
        (F.T.map (CR.counit.app P) ≫ F.ε.app ((quotientRoos R t).obj P)) = _
      calc
        _ = F.T.map (CR.unit.app (DerivedCategory.Q.obj P) ≫ CR.counit.app P) ≫
            F.ε.app ((quotientRoos R t).obj P) := by
          simp only [Functor.map_comp, Category.assoc]
        _ = F.T.map (DerivedCategory.Q.map (CR.augmentation P)) ≫
            F.ε.app ((quotientRoos R t).obj P) :=
          congrArg (fun f ↦ F.T.map f ≫ F.ε.app ((quotientRoos R t).obj P))
            (CR.unit_computes P)
        _ = _ := F.ε.naturality (CR.augmentation P)
    have hr : CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) ≫ β.app P =
        F.ε.app P ≫ DerivedCategory.Q.map (CS.augmentation (EC.obj P)) := by
      have hn := CS.unit.naturality (F.ε.app P)
      change F.ε.app P ≫ CS.unit.app (DerivedCategory.Q.obj (EC.obj P)) =
        CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) ≫
          CS.completion.map (F.ε.app P) at hn
      change CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) ≫
        (CS.completion.map (F.ε.app P) ≫ CS.counit.app (EC.obj P)) = _
      calc
        _ = (CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) ≫
            CS.completion.map (F.ε.app P)) ≫ CS.counit.app (EC.obj P) :=
          (Category.assoc _ _ _).symm
        _ = (F.ε.app P ≫ CS.unit.app (DerivedCategory.Q.obj (EC.obj P))) ≫
            CS.counit.app (EC.obj P) :=
          congrArg (· ≫ CS.counit.app (EC.obj P)) hn.symm
        _ = F.ε.app P ≫ (CS.unit.app (DerivedCategory.Q.obj (EC.obj P)) ≫
            CS.counit.app (EC.obj P)) := Category.assoc _ _ _
        _ = _ := congrArg (F.ε.app P ≫ ·) (CS.unit_computes (EC.obj P))
    apply (cancel_mono (β.app P ≫ DerivedCategory.Q.map (D.a P))).1
    calc
      _ = (F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫ α.app P) ≫
          DerivedCategory.Q.map (D.δ P).hom := by
        simpa only [Category.assoc] using
          congrArg (F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫ ·) (hformula P hP)
      _ = (F.ε.app P ≫ DerivedCategory.Q.map (EC.map (CR.augmentation P))) ≫
          DerivedCategory.Q.map (D.δ P).hom :=
        congrArg (· ≫ DerivedCategory.Q.map (D.δ P).hom) hl
      _ = (F.ε.app P ≫ DerivedCategory.Q.map (CS.augmentation (EC.obj P))) ≫
          DerivedCategory.Q.map (D.a P) := by
        have hh := congrArg (fun f ↦ F.ε.app P ≫ DerivedCategory.Q.map f)
          (augmentationSquare F t vS e D CR CS P)
        simpa only [Functor.map_comp, Category.assoc] using hh
      _ = (CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) ≫ β.app P) ≫
          DerivedCategory.Q.map (D.a P) :=
        congrArg (· ≫ DerivedCategory.Q.map (D.a P)) hr.symm
      _ = _ := Category.assoc _ _ _
  have hu : ∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CS.unit.app (F.T.obj Q) := by
    let γ : F.T ⟶ V :=
      (Functor.leftUnitor F.T).inv ≫ Functor.whiskerRight CR.unit F.T ≫ ε.hom
    have hg : γ = Functor.whiskerLeft F.T CS.unit := by
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ))
      intro P
      obtain ⟨K, f, hK, _, hf, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
      let : QuasiIso f := hf
      apply (cancel_epi (F.T.map (DerivedCategory.Q.map f))).1
      change F.T.map (DerivedCategory.Q.map f) ≫ γ.app (DerivedCategory.Q.obj P) =
        F.T.map (DerivedCategory.Q.map f) ≫
          CS.unit.app (F.T.obj (DerivedCategory.Q.obj P))
      have hγK : γ.app (DerivedCategory.Q.obj K) =
          CS.unit.app (F.T.obj (DerivedCategory.Q.obj K)) := by
        simpa only [γ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
          Functor.whiskerRight_app, Category.id_comp] using hunit K hK
      exact (γ.naturality (DerivedCategory.Q.map f)).trans
        ((congrArg (· ≫ V.map (DerivedCategory.Q.map f)) hγK).trans
          (CS.unit.naturality (F.T.map (DerivedCategory.Q.map f))).symm)
    intro Q
    simpa only [γ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp] using
        NatTrans.congr_app hg Q
  refine ⟨ε, hu, ?_⟩
  intro P hP
  refine ⟨⟨{ β := D.β P
             c := D.c P
             product_formula := D.product_formula P
             δ := D.δ P
             cone_formula := D.cone_formula P
             a := D.a P
             arithmetic_quasiIso := D.arithmetic_quasiIso P
             arithmetic_formula := D.arithmetic_formula P },
      D.quotient_formula P, ?_⟩⟩
  change ε.hom.app (DerivedCategory.Q.obj P) ≫
    CS.completion.map (F.ε.app P) ≫ CS.counit.app (EC.obj P) ≫
      DerivedCategory.Q.map (D.a P) =
    F.T.map (CR.counit.app P) ≫ F.ε.app ((quotientRoos R t).obj P) ≫
      DerivedCategory.Q.map (D.δ P).hom
  have hh := hformula P hP
  change ε.hom.app (DerivedCategory.Q.obj P) ≫
    (CS.completion.map (F.ε.app P) ≫ CS.counit.app (EC.obj P)) ≫
      DerivedCategory.Q.map (D.a P) =
    (F.T.map (CR.counit.app P) ≫ F.ε.app ((quotientRoos R t).obj P)) ≫
      DerivedCategory.Q.map (D.δ P).hom at hh
  simpa only [Category.assoc] using hh

end CategoryTheory.PrincipalQuotientCompletion
