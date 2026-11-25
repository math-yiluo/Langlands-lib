/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Homology.SmoothPurity.ChangeOfRingsTensorCancellationIndependentCoefficientsSupplement
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionExists
import WeilConjectures.CategoryTheory.Roos.RoosComparisonHorizontalCoherenceSupplement
import all WeilConjectures.CategoryTheory.CofinalRoos.CofinalRoosRestriction
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all WeilConjectures.CategoryTheory.Finite.FiniteFreeStrictTowerTransport
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Cochain comparisons for finite free principal quotient towers

Source: Stacks Project, sites-cohomology.tex, Tags 06YT and 0941, and the
balanced quotient calculation in lem-pur-finite-free-completion-exchange.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
namespace CategoryTheory.PrincipalQuotientCompletion

attribute [local irreducible] quotientTower roosF roosχ

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

local instance (T : Sheaf J CommRingCat.{r}) (I : Type r) :
    HasColimitsOfShape (Discrete I)
      (PresheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J T).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- Cochain data for scalar extension of principal quotient towers. No derived
completion functor occurs here. Naturality is required for all cochain maps.
Source: the balanced quotient calculation and additive cone construction in steps
1--5 of lem-pur-finite-free-completion-exchange
(blueprint: lem-pur-finite-free-quotient-roos-comparison). -/
structure QuotientRoosExchange
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections) (e : ℕ) where
  exact_limits : PreservesFiniteLimits F.E
  exact_colimits : PreservesFiniteColimits F.E
  β : ∀ P, ((quotientTower R t).obj P).asFunctor ⋙
      F.E.mapHomologicalComplex (.up ℤ) ≅
    index e ⋙ ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor
  c : ∀ P, (F.E.mapHomologicalComplex (.up ℤ)).obj
      (roosP ((quotientTower R t).obj P)) ⟶
    roosP ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  product_formula : ∀ P (n : ℕ),
    c P ≫ Pi.π _ n = (F.E.mapHomologicalComplex (.up ℤ)).map
      (Pi.π (fun k : ℕ ↦ ((quotientTower R t).obj P).asFunctor.obj (op k)) n) ≫
        (β P).hom.app (op n)
  quotient_formula : ∀ P (n : ℕ),
    (F.E.mapHomologicalComplex (.up ℤ)).map (quotientMap R t P n) ≫
      (β P).hom.app (op n) = quotientMap S vS
        ((F.E.mapHomologicalComplex (.up ℤ)).obj P) (e * (n + 1) - 1)
  δ : ∀ P, (F.E.mapHomologicalComplex (.up ℤ)).obj ((quotientRoos R t).obj P) ≅
    roosF.obj ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  cone_formula : ∀ P (p : ℤ),
    (δ P).hom.f (p + 1) ≫ (roosχ ((complexRestriction _ e).obj
      ((quotientTower S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P))) p).hom =
    biprod.lift
      (F.E.map ((roosχ ((quotientTower R t).obj P) p).hom ≫ biprod.fst) ≫ (c P).f p)
      (F.E.map ((roosχ ((quotientTower R t).obj P) p).hom ≫ biprod.snd) ≫
        (c P).f (p + 1))
  a : ∀ P, (quotientRoos S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P) ⟶
    roosF.obj ((complexRestriction _ e).obj ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)))
  arithmetic_quasiIso : ∀ P, QuasiIso (a P)
  arithmetic_formula : ∀ P (p : ℤ),
    (a P).f (p + 1) ≫ (roosχ ((complexRestriction _ e).obj
      ((quotientTower S vS).obj ((F.E.mapHomologicalComplex (.up ℤ)).obj P))) p).hom =
    (roosχ ((quotientTower S vS).obj
      ((F.E.mapHomologicalComplex (.up ℤ)).obj P)) p).hom ≫
      biprod.map
        ((block e ((quotientTower S vS).obj
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor).f p)
        ((selection e ((quotientTower S vS).obj
          ((F.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor).f (p + 1))
  delta_natural : ∀ {P P'} (f : P ⟶ P'),
    (F.E.mapHomologicalComplex (.up ℤ)).map ((quotientRoos R t).map f) ≫ (δ P').hom =
      (δ P).hom ≫ roosF.map ((complexRestriction _ e).map
        ((quotientTower S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f)))
  arithmetic_natural : ∀ {P P'} (f : P ⟶ P'),
    (quotientRoos S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f) ≫ a P' =
      a P ≫ roosF.map ((complexRestriction _ e).map
        ((quotientTower S vS).map ((F.E.mapHomologicalComplex (.up ℤ)).map f)))

attribute [local semireducible] roosF

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance] SheafOfModules.symmetricCategory

open SheafOfModules MonoidalCategory

attribute [local irreducible] SheafOfModules.tensorFreePowerIso

private theorem restrictedTensor
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ) :
    Nonempty (D.E ⋙ restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      tensorLeft ((restrictScalars.{r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          (unit (derivedChangeRingIndependentCoefficients J S)))) := by
  let U := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  let N := U.obj (unit (derivedChangeRingIndependentCoefficients J S))
  obtain ⟨e, he⟩ := exists_changeOfRings_tensorCancellation_independentCoefficients φ
  let i (M) : U.obj (D.E.obj M) ≅ N ⊗ M :=
    U.mapIso (eqToIso (D.obj_eq M)) ≪≫
      U.mapIso (MonoidalCategory.leftUnitor (changeOfRings φ M)).symm ≪≫
      e (unit (derivedChangeRingIndependentCoefficients J S)) M
  refine ⟨NatIso.ofComponents i ?_⟩
  intro M M' f
  dsimp only [i, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.comp_map, MonoidalCategory.tensorLeft]
  rw [D.map_eq]
  dsimp only [U]
  simp only [Functor.map_comp, eqToIso.hom, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Functor.map_comp,
    Category.assoc]
  have hn := congrArg U.map
    ((MonoidalCategory.leftUnitorNatIso _).inv.naturality (changeOfRingsHom φ M f))
  simp only [Functor.map_comp] at hn
  change U.map (changeOfRingsHom φ M f) ≫ U.map (λ_ _).inv =
    U.map (λ_ _).inv ≫ U.map (_ ◁ changeOfRingsHom φ M f) at hn
  rw [reassoc_of% hn]
  have hc : U.map (𝟙_ _ ◁ changeOfRingsHom φ M f) ≫
      (e (unit (derivedChangeRingIndependentCoefficients J S)) M').hom =
      (e (unit (derivedChangeRingIndependentCoefficients J S)) M).hom ≫
        (tensorLeft N).map f := by
    have hc := he (𝟙 (unit (derivedChangeRingIndependentCoefficients J S))) f
    change U.map (_ ⊗ₘ changeOfRingsHom φ M f) ≫ _ =
      _ ≫ (U.map (𝟙 _) ⊗ₘ f) at hc
    rw [U.map_id, id_tensorHom, id_tensorHom] at hc
    exact hc
  rw [hc]

private theorem scalarExactProducts
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty ((restrictScalars.{r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (unit (derivedChangeRingIndependentCoefficients J S)) ≅
          ∐ (fun _ : Fin d ↦ unit (derivedChangeRingIndependentCoefficients J R)))) :
    PreservesFiniteLimits D.E ∧ PreservesFiniteColimits D.E ∧
      PreservesLimitsOfShape (Discrete ℕ) D.E := by
  classical
  let U := restrictScalars.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  obtain ⟨d, ⟨e⟩⟩ := hfree
  obtain ⟨i⟩ := restrictedTensor D
  let j : D.E ⋙ U ≅ Functor.const (Discrete (Fin d)) ⋙ lim :=
    i ≪≫ (tensoringLeft (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R))).mapIso e ≪≫
    tensorFreePowerIso _ (Fin d) (Iso.refl _)
  have hlim : PreservesLimitsOfSize.{0, 0} (D.E ⋙ U) :=
    preservesLimits_of_natIso j.symm
  obtain ⟨href, hlimU, _⟩ := scalarRestrictionProperties
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : HasLimitsOfSize.{r, r}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)) :=
    (moduleSheaves_colimits_forgetful
      (derivedChangeRingIndependentCoefficients J S)).2.2.2.1
  have : HasLimitsOfSize.{0, 0}
      (ringedSiteModules.{r} (derivedChangeRingIndependentCoefficients J S)) :=
    hasLimitsOfSizeShrink _
  have : U.ReflectsIsomorphisms := href
  have : PreservesLimitsOfSize.{r, r} U := hlimU
  have : PreservesLimitsOfSize.{0, 0} U := preservesLimitsOfSize_shrink _
  have : ReflectsLimitsOfSize.{0, 0} U := reflectsLimits_of_reflectsIsomorphisms
  have : PreservesLimitsOfSize.{0, 0} D.E := preservesLimits_of_reflects_of_preserves D.E U
  obtain ⟨_, _, h⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, _⟩ := h D.E D.obj_eq D.map_eq
  have : PreservesColimits D.E := adj.leftAdjoint_preservesColimits
  exact ⟨inferInstance, inferInstance, inferInstance⟩

open SheafOfModules.IndependentExtensionTensor SheafOfModules.RegularQuotientCone

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarPower_apply (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (M : Modules R) (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj U) :
    (endoPow ((scalar R t).app M) n).val.app U x = ((@id (R.obj.obj U) (t.val U))) ^ n • x := by
  induction n with
  | zero => change x = ((@id (R.obj.obj U) (t.val U))) ^ 0 • x; simp
  | succ n ih =>
    change ((@id (R.obj.obj U) (t.val U))) • ((endoPow ((scalar R t).app M) n).val.app U x) = _
    rw [ih, smul_smul, pow_succ']

omit [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalar_unit (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
    globalSectionMultiplication R t =
      (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let x : R.obj.obj U := x
  change x * (@id (R.obj.obj U) (t.val U)) = (@id (R.obj.obj U) (t.val U)) * x
  exact mul_comm _ _

private noncomputable def moduleUnitIso (R : Sheaf J CommRingCat.{r})
    (M : Modules R) : unit (derivedChangeRingIndependentCoefficients J R) ⊗ M ≅ M := λ_ M

attribute [local irreducible] moduleUnitIso SheafOfModules.monoidalCategory

attribute [local semireducible] SheafOfModules.monoidalCategory in
private theorem regularTensorIso_eq
    {A : Type*} [Category A] [EssentiallySmall.{u} A]
    {J : GrothendieckTopology A}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.IndependentExtensionTensor.regularTensorIso M = moduleUnitIso R M := by
  unfold moduleUnitIso
  apply Iso.ext
  dsimp only [SheafOfModules.IndependentExtensionTensor.regularTensorIso,
    SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_inv, Iso.app_inv, asIso_inv]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.map_leftUnitor,
    Category.assoc]
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
  change (e.app (SheafOfModules.unit _) ⊗ᵢ e.app M).inv ≫
    Functor.LaxMonoidal.μ F (𝟙_ _) M.val ≫
    Functor.OplaxMonoidal.δ F (𝟙_ _) M.val ≫
    (SheafOfModules.sheafificationObjUnitIso R).hom ▷ F.obj M.val ≫
    (λ_ (F.obj M.val)).hom ≫ (e.app M).hom = _
  rw [Functor.Monoidal.μ_δ_assoc]
  simp only [SheafOfModules.sheafificationObjUnitIso, tensorIso_inv, tensorHom_def',
    Category.assoc, ← leftUnitor_naturality]
  change (𝟙_ _) ◁ (e.app M).inv ≫
    (e.app (SheafOfModules.unit _)).inv ▷ F.obj M.val ≫
    (e.app (SheafOfModules.unit _)).hom ▷ F.obj M.val ≫
    (𝟙_ _) ◁ (e.app M).hom ≫ (λ_ M).hom = _
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, ← whiskerLeft_comp_assoc, whiskerLeft_id]

attribute [local semireducible] quotientTower in
private noncomputable def quotientDegreeIso (R : Sheaf J CommRingCat.{r})
    (a : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (Modules R) ℤ) (n : ℕ) (i : ℤ) :
    (((quotientTower R a).obj P).asFunctor.obj (op n)).X i ≅
      principalQuotient R a n ⊗ P.X i :=
  (HomologicalComplex.eval _ _ i).mapIso
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R))
      (principalQuotient R a n) P)

attribute [local semireducible] quotientTower in
attribute [local semireducible] moduleUnitIso SheafOfModules.monoidalCategory in
private theorem single_tensor_quotient_component
    (R : Sheaf J CommRingCat.{r})
    (a : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ) (n : ℕ) (i : ℤ) :
    (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫
        (quotientDegreeIso R a P n i).hom =
      (moduleUnitIso R (P.X i)).inv ≫
        cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)) ▷ P.X i := by
  dsimp only [quotientDegreeIso, Functor.mapIso_hom, HomologicalComplex.eval_map]
  apply (cancel_mono
    ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor (Modules R))
      (principalQuotient R a n) P).inv.f i)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    Category.comp_id]
  simp only [PrincipalQuotientCompletion.quotientMap, koszulRepresentativeQuotient,
    HomologicalComplex.comp_f, koszulTensorUnitInclusion, koszulTensorUnitComponent,
    koszulTensorFunctor, Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.id_f, curriedTensor_map_app, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id_assoc]
  dsimp only [curriedTensor_obj_map]
  simp only [whiskerLeft_id]
  rfl

attribute [local irreducible] quotientDegreeIso

private theorem scalar_tensor (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (M : Modules R) (n : ℕ) :
    endoPow ((scalar R t).app M) n ≫ (moduleUnitIso R M).inv =
      (moduleUnitIso R M).inv ≫ (endoPow (globalSectionMultiplication R t) n) ▷ M := by
  rw [← regularTensorIso_eq R M, scalar_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (regularTensorIso M).inv.val.app U
    ((endoPow ((scalar R t).app M) n).val.app U x) =
    (((endoPow ((scalar R t).app (unit
      (derivedChangeRingIndependentCoefficients J R))) n) ▷ M).val.app U)
      ((regularTensorIso M).inv.val.app U x)
  rw [scalarPower_apply, regularTensorIso_inv_apply, regularTensorIso_inv_apply]
  erw [tensorPresheafUnit_whiskerRight_apply]
  rw [scalarPower_apply]
  simp only [smul_eq_mul, mul_one]
  apply congrArg ((tensorPresheafUnit (unit
    (derivedChangeRingIndependentCoefficients J R)) M).app U)
  change (1 : R.obj.obj U) ⊗ₜ[R.obj.obj U]
      ((@id (R.obj.obj U) (t.val U)) ^ n • x) =
    ((@id (R.obj.obj U) (t.val U)) ^ n) ⊗ₜ[R.obj.obj U] x
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [smul_eq_mul, mul_one]

private theorem quotientCokernel (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (Modules R) ℤ) (n : ℕ) (i : ℤ) :
    ∃ h : endoPow ((scalar R t).app (P.X i)) (n + 1) ≫
        (quotientMap R t P n).f i = 0,
      Nonempty (IsColimit (CokernelCofork.ofπ ((quotientMap R t P n).f i) h)) := by
  classical
  have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R (P.X i)
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft (P.X i)) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, 0} (tensorRight (P.X i)) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  let f := endoPow (globalSectionMultiplication R t) (n + 1)
  let g := endoPow ((scalar R t).app (P.X i)) (n + 1)
  let q := (quotientMap R t P n).f i
  let k := quotientDegreeIso R t P n i
  have hq := single_tensor_quotient_component R t P n i
  have hzero : g ≫ q = 0 := by
    apply (cancel_mono (k.hom)).1
    erw [Category.assoc, hq, ← Category.assoc, scalar_tensor,
      Category.assoc, ← comp_whiskerRight, cokernel.condition,
      MonoidalPreadditive.zero_whiskerRight, comp_zero, zero_comp]
  let cc : CokernelCofork f := CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)
  have hcc : IsColimit cc := cokernelIsCokernel f
  let cc' := cc.map (tensorRight (P.X i))
  have hcc' : IsColimit cc' :=
    CokernelCofork.mapIsColimit cc hcc (tensorRight (P.X i))
  refine ⟨hzero, ⟨?_⟩⟩
  exact IsCokernel.ofIso
    ((tensorRight (P.X i)).map f)
    hcc'
    (CokernelCofork.ofπ q hzero) (moduleUnitIso R (P.X i)) (moduleUnitIso R (P.X i))
    k.symm
    (by
      apply (cancel_epi (moduleUnitIso R (P.X i)).inv).1
      simp only [Iso.inv_hom_id_assoc]
      apply (cancel_mono (moduleUnitIso R (P.X i)).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact scalar_tensor R t (P.X i) (n + 1))
    (by
      apply (cancel_epi (moduleUnitIso R (P.X i)).inv).1
      simp only [Iso.inv_hom_id_assoc]
      apply (cancel_mono (k.hom)).1
      change q ≫ k.hom = (moduleUnitIso R (P.X i)).inv ≫
        (cokernel.π f ▷ P.X i) ≫ k.inv ≫ k.hom
      simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hq)

attribute [local irreducible] quotientMap

private theorem scalar_power_extension
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (vS uS : (unit (derivedChangeRingIndependentCoefficients J S)).sections)
    (e n : ℕ)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    (M : Modules R) :
    D.E.map (endoPow ((scalar R t).app M) n) =
      endoPow ((scalar S uS).app (D.E.obj M)) n ≫
        endoPow ((scalar S vS).app (D.E.obj M)) (e * n) := by
  obtain ⟨_, _, ha⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adj, _⟩ := ha D.E D.obj_eq D.map_eq
  apply (adj.homEquiv M (D.E.obj M)).injective
  rw [← Category.comp_id (D.E.map _), adj.homEquiv_naturality_left]
  dsimp only [Functor.id_obj]
  rw [adj.homEquiv_id, adj.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (adj.unit.app M).val.app U
      ((endoPow ((scalar R t).app M) n).val.app U x) =
    (endoPow ((scalar S vS).app (D.E.obj M)) (e * n)).val.app U
      ((endoPow ((scalar S uS).app (D.E.obj M)) n).val.app U
        ((adj.unit.app M).val.app U x))
  rw [scalarPower_apply,
    ((adj.unit.app M).val.app U).hom.map_smul]
  let y : (D.E.obj M).val.obj U := (adj.unit.app M).val.app U x
  change (φ.hom.app U ((@id (R.obj.obj U) (t.val U)) ^ n)) • y = _
  rw [scalarPower_apply, scalarPower_apply, smul_smul, map_pow, hrelation,
    mul_pow, ← pow_mul]
  rw [mul_comm]

omit [EssentiallySmall.{r} C] [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasDerivedCategory.{wS} (Modules S)] in
private theorem scalar_power_isIso
    (uS : (unit (derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit ((@id (S.obj.obj U) (uS.val U)))) (M : Modules S) (n : ℕ) :
    IsIso (endoPow ((scalar S uS).app M) n) := by
  have hi : IsIso ((scalar S uS).app M) := by
    let hU (U : Cᵒᵖ) : IsIso (((scalar S uS).app M).val.app U) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (fun x : M.val.obj U ↦ (@id (S.obj.obj U) (uS.val U)) • x)
      exact (hu U).smul_bijective
    have : IsIso ((scalar S uS).app M).val := by
      let k := PresheafOfModules.isoMk
        (fun U ↦ asIso (((scalar S uS).app M).val.app U))
        (by intro U V f; exact ((scalar S uS).app M).val.naturality f)
      have hk : k.hom = ((scalar S uS).app M).val := rfl
      rw [← hk]
      infer_instance
    have : IsIso ((SheafOfModules.forget _).map ((scalar S uS).app M)) :=
      inferInstanceAs (IsIso ((scalar S uS).app M).val)
    exact isIso_of_reflects_iso ((scalar S uS).app M) (SheafOfModules.forget _)
  induction n with
  | zero => change IsIso (𝟙 M); infer_instance
  | succ n ih =>
    change IsIso (endoPow ((scalar S uS).app M) n ≫ (scalar S uS).app M)
    infer_instance

attribute [local irreducible] scalar globalSectionMultiplication endoPow principalQuotient

set_option backward.isDefEq.respectTransparency true in
private theorem quotient_component
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [PreservesFiniteColimits D.E]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (vS uS : (unit (derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit ((@id (S.obj.obj U) (uS.val U)))) (e : ℕ) (he : 1 ≤ e)
    (hr : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    (P : CochainComplex (Modules R) ℤ) (n : ℕ) (i : ℤ) :
    ∃ b : D.E.obj ((((quotientTower R t).obj P).asFunctor.obj (op n)).X i) ≅
        ((((quotientTower S vS).obj
          ((D.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor.obj
            (op (e * (n + 1) - 1))).X i),
      D.E.map ((quotientMap R t P n).f i) ≫ b.hom =
        (quotientMap S vS ((D.E.mapHomologicalComplex (.up ℤ)).obj P)
          (e * (n + 1) - 1)).f i := by
  classical
  obtain ⟨hz, ⟨hc⟩⟩ := quotientCokernel R t P n i
  obtain ⟨hz', ⟨hc'⟩⟩ := quotientCokernel S vS
    ((D.E.mapHomologicalComplex (.up ℤ)).obj P) (e * (n + 1) - 1) i
  have hn : e * (n + 1) - 1 + 1 = e * (n + 1) := by
    have hp : 1 ≤ e * (n + 1) := Nat.mul_pos (by omega) (by omega)
    omega
  let Q := (D.E.mapHomologicalComplex (.up ℤ)).obj P
  let q := (quotientMap S vS Q (e * (n + 1) - 1)).f i
  let K (m : ℕ) : Prop := ∃ h : endoPow ((scalar S vS).app (Q.X i)) m ≫ q = 0,
    Nonempty (IsColimit (CokernelCofork.ofπ q h))
  have h0 : K (e * (n + 1) - 1 + 1) := ⟨hz', ⟨hc'⟩⟩
  have h1 : K (e * (n + 1)) := hn ▸ h0
  obtain ⟨hz', ⟨hc'⟩⟩ := h1
  let hi : IsIso (endoPow ((scalar S uS).app (D.E.obj (P.X i))) (n + 1)) :=
    scalar_power_isIso uS hu (D.E.obj (P.X i)) (n + 1)
  let hc'' := isCokernelEpiComp hc'
    (endoPow ((scalar S uS).app (D.E.obj (P.X i))) (n + 1))
    (hg := @IsIso.epi_of_iso _ _ _ _ _ hi)
    (scalar_power_extension D t vS uS e (n + 1) hr (P.X i))
  let hE := CokernelCofork.mapIsColimit _ hc D.E
  let b := CokernelCofork.mapIsoOfIsColimit hE hc'' (Iso.refl _)
  refine ⟨b, ?_⟩
  exact (CokernelCofork.π_mapOfIsColimit hE _ (𝟙 _)).trans (Category.id_comp _)

private theorem quotient_epi
    (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (Modules R) ℤ) (n : ℕ) (i : ℤ) :
    Epi ((quotientMap R t P n).f i) := by
  obtain ⟨_, ⟨hc⟩⟩ := quotientCokernel R t P n i
  exact epi_of_isColimit_cofork hc

private theorem balancedTower
    (D : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [PreservesFiniteColimits D.E]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (vS uS : (unit (derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit ((@id (S.obj.obj U) (uS.val U)))) (e : ℕ) (he : 1 ≤ e)
    (hr : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e) :
    ∃ β : ∀ P, ((quotientTower R t).obj P).asFunctor ⋙
        D.E.mapHomologicalComplex (.up ℤ) ≅
      index e ⋙ ((quotientTower S vS).obj
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P)).asFunctor,
      ∀ P n, (D.E.mapHomologicalComplex (.up ℤ)).map (quotientMap R t P n) ≫
        (β P).hom.app (op n) = quotientMap S vS
          ((D.E.mapHomologicalComplex (.up ℤ)).obj P) (e * (n + 1) - 1) := by
  classical
  let G := D.E.mapHomologicalComplex (.up ℤ)
  choose b hb using quotient_component D t vS uS hu e he hr
  let epiq (P : CochainComplex (Modules R) ℤ) (n : ℕ) (i : ℤ) :
      Epi (D.E.map ((quotientMap R t P n).f i)) := by
    have := quotient_epi R t P n i
    infer_instance
  let k (P : CochainComplex (Modules R) ℤ) (n : ℕ) :
      G.obj (((quotientTower R t).obj P).asFunctor.obj (op n)) ≅
        ((quotientTower S vS).obj (G.obj P)).asFunctor.obj
          (op (e * (n + 1) - 1)) :=
    HomologicalComplex.Hom.isoOfComponents (b P n) (by
      intro i j hij
      apply (cancel_epi (D.E.map ((quotientMap R t P n).f i))).1
      change D.E.map ((quotientMap R t P n).f i) ≫
        ((b P n i).hom ≫ _) =
        D.E.map ((quotientMap R t P n).f i) ≫ (D.E.map _ ≫ (b P n j).hom)
      rw [← Category.assoc, hb, ← Category.assoc, ← D.E.map_comp,
        (quotientMap R t P n).comm i j, D.E.map_comp, Category.assoc, hb]
      exact (quotientMap S vS (G.obj P) (e * (n + 1) - 1)).comm i j)
  have hk (P : CochainComplex (Modules R) ℤ) (n : ℕ) :
      G.map (quotientMap R t P n) ≫ (k P n).hom =
        quotientMap S vS (G.obj P) (e * (n + 1) - 1) := by
    ext i : 1
    exact hb P n i
  refine ⟨fun P ↦ NatIso.ofComponents (fun n ↦ k P n.unop) ?_, hk⟩
  intro n m f
  have : Epi (quotientMap R t P n.unop) := by
    exact HomologicalComplex.epi_of_epi_f _
      (fun i ↦ quotient_epi R t P n.unop i)
  have : Epi (G.map (quotientMap R t P n.unop)) := inferInstance
  apply (cancel_epi (G.map (quotientMap R t P n.unop))).1
  have hn := roos_compatible ((quotientTower R t).obj P).asFunctor
    (quotientMap R t P) (quotient_transition R t P) (leOfHom f.unop)
  have hm := roos_compatible ((quotientTower S vS).obj (G.obj P)).asFunctor
    (quotientMap S vS (G.obj P)) (quotient_transition S vS (G.obj P))
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left e
        (Nat.add_le_add_right (leOfHom f.unop) 1)) 1)
  change G.map (quotientMap R t P n.unop) ≫
    (G.map (((quotientTower R t).obj P).asFunctor.map f) ≫ (k P m.unop).hom) =
    G.map (quotientMap R t P n.unop) ≫
      ((k P n.unop).hom ≫
        ((quotientTower S vS).obj (G.obj P)).asFunctor.map ((index e).map f))
  have hn' : quotientMap R t P n.unop ≫
      ((quotientTower R t).obj P).asFunctor.map f = quotientMap R t P m.unop := by
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    rw [hf]
    exact hn
  have hm' : quotientMap S vS (G.obj P) (e * (n.unop + 1) - 1) ≫
      ((quotientTower S vS).obj (G.obj P)).asFunctor.map ((index e).map f) =
        quotientMap S vS (G.obj P) (e * (m.unop + 1) - 1) := by
    convert hm using 1 <;> rfl
  rw [← Category.assoc, ← G.map_comp, hn', hk, ← Category.assoc, hk]
  exact hm'.symm


private def arithmeticEmbedding (e : ℕ) (he : 1 ≤ e) : ℕ ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun n ↦ e * (n + 1) - 1) (by
    intro n m h
    dsimp only
    have hn : 1 ≤ e * (n + 1) := by nlinarith
    have hm : e * (n + 1) < e * (m + 1) := by nlinarith
    omega)

private theorem arithmeticBlock
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (e : ℕ) (he : 1 ≤ e) :
    CofinalRoos.block X (arithmeticEmbedding e he) = block e X.asFunctor := by
  apply Pi.hom_ext
  intro n
  simp only [CofinalRoos.block, block, Pi.lift_comp_π]
  have hn : 1 ≤ e * (n + 1) := by nlinarith
  have hd : e * (n + 1 + 1) - 1 - (e * (n + 1) - 1) = e := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  change (∑ k ∈ Finset.range (e * (n + 1 + 1) - 1 - (e * (n + 1) - 1)),
    _) = _
  rw [hd]
  dsimp only [arithmeticEmbedding, OrderEmbedding.ofStrictMono]
  erw [Pi.lift_comp_π]
  rfl

private theorem arithmeticRoos
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (e : ℕ) (he : 1 ≤ e) :
    ∃ a : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      roosF.obj X ⟶ roosF.obj ((complexRestriction A e).obj X),
      (∀ X, QuasiIso (a X)) ∧
      (∀ X p, (a X).f (p + 1) ≫
        (roosχ ((complexRestriction A e).obj X) p).hom =
        (roosχ X p).hom ≫ biprod.map ((block e X.asFunctor).f p)
          ((selection e X.asFunctor).f (p + 1))) ∧
      (∀ {X Y} (f : X ⟶ Y), roosF.map f ≫ a Y =
        a X ≫ roosF.map ((complexRestriction A e).map f)) := by
  let φ := arithmeticEmbedding e he
  refine ⟨fun X ↦ CofinalRoos.rho X φ, fun X ↦ CofinalRoos.rho_quasiIso X φ,
    ?_, fun f ↦ CofinalRoos.rho_natural f φ⟩
  intro X p
  have h := CofinalRoos.rho_coord X φ p
  rw [show CofinalRoos.block X φ = block e X.asFunctor from arithmeticBlock X e he] at h
  exact h

private abbrev roosTowerMap
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (E : A ⥤ B) [E.Additive] := roosTowerAction E

private noncomputable abbrev roosComparison
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :=
  roosProductComparison E X

private noncomputable def transposeIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (β : X.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ Y.asFunctor) :
    ((((Functor.whiskeringRight ℕᵒᵖ A B).obj E).mapHomologicalComplex
      (.up ℤ)).obj X) ≅ Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ NatIso.ofComponents (fun n ↦
      (HomologicalComplex.eval B (.up ℤ) i).mapIso (β.app n)) (by
        intro n m f
        exact congrArg (fun z ↦ z.f i) (β.hom.naturality f))) (by
          intro i j hij
          ext n
          exact (β.hom.app n).comm i j)

private theorem transposeIso_hom_f_app
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (β : X.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ Y.asFunctor)
    (i : ℤ) (n : ℕᵒᵖ) :
    ((transposeIso E X Y β).hom.f i).app n = (β.hom.app n).f i := rfl

private theorem transposeIso_natural
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (E : A ⥤ B) [E.Additive]
    {X X' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {Y Y' : CochainComplex (ℕᵒᵖ ⥤ B) ℤ}
    (β : X.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ Y.asFunctor)
    (β' : X'.asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅ Y'.asFunctor)
    (f : X ⟶ X') (g : Y ⟶ Y')
    (h : ∀ n, (E.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app n) ≫
          β'.hom.app n = β.hom.app n ≫
            (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map g).app n) :
    ((roosTowerMap E).map f) ≫ (transposeIso E X' Y' β').hom =
      (transposeIso E X Y β).hom ≫ g := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext n
  exact congrArg (fun z ↦ z.f i) (h n)

attribute [local irreducible] transposeIso

private theorem roosPostCoordinates
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) E] (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (b : (roosTowerMap E).obj X ≅ Y) (p : ℤ) :
    ((roosAdditiveComparison E X ≫ roosF.map b.hom).f (p + 1)) ≫ (roosχ Y p).hom =
      biprod.lift
        (E.map ((roosχ X p).hom ≫ biprod.fst) ≫
          (roosComparison E X ≫ roosPmap b.hom).f p)
        (E.map ((roosχ X p).hom ≫ biprod.snd) ≫
          (roosComparison E X ≫ roosPmap b.hom).f (p + 1)) := by
  simp only [HomologicalComplex.comp_f, Category.assoc, roosF_map_χ]
  rw [← Category.assoc]
  erw [roosAdditiveComparison_coordinates]
  apply biprod.hom_ext <;> simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd]
  · erw [biprod.map_fst, biprod.map_fst_assoc,
      Functor.biprodComparison_fst_assoc, ← E.map_comp_assoc]
  · erw [biprod.map_snd, biprod.map_snd_assoc,
      Functor.biprodComparison_snd_assoc, ← E.map_comp_assoc]

private noncomputable def actualRoosPost
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) E] (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (b : (roosTowerMap E).obj X ≅ Y) :
    (E.mapHomologicalComplex (.up ℤ)).obj (roosF.obj X) ≅ roosF.obj Y :=
  (by
    have := roosAdditiveComparison_isIso E X
    exact asIso (roosAdditiveComparison E X) ≪≫ roosF.mapIso b)

attribute [local irreducible] actualRoosPost

private theorem actualRoosPost_coordinates
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) E] (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (b : (roosTowerMap E).obj X ≅ Y) (p : ℤ) :
    (actualRoosPost E X Y b).hom.f (p + 1) ≫ (roosχ Y p).hom =
      biprod.lift
        (E.map ((roosχ X p).hom ≫ biprod.fst) ≫
          (roosComparison E X ≫ roosPmap b.hom).f p)
        (E.map ((roosχ X p).hom ≫ biprod.snd) ≫
          (roosComparison E X ≫ roosPmap b.hom).f (p + 1)) := by
  unfold actualRoosPost
  exact roosPostCoordinates E X Y b p

private theorem actualRoosPost_natural
    {A B : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    [Category B] [Abelian B] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive]
    {X X' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    [PreservesLimitsOfShape (Discrete ℕ) E]
    {Y Y' : CochainComplex (ℕᵒᵖ ⥤ B) ℤ}
    (b : (roosTowerMap E).obj X ≅ Y) (b' : (roosTowerMap E).obj X' ≅ Y')
    (f : X ⟶ X') (k : Y ⟶ Y')
    (hb : (roosTowerMap E).map f ≫ b'.hom = b.hom ≫ k) :
    (E.mapHomologicalComplex (.up ℤ)).map (roosF.map f) ≫
      (actualRoosPost E X' Y' b').hom =
      (actualRoosPost E X Y b).hom ≫ roosF.map k := by
  unfold actualRoosPost
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  rw [← Category.assoc, roosAdditiveComparison_natural E f, Category.assoc,
    ← roosF.map_comp, hb, roosF.map_comp, ← Category.assoc]

private theorem towerRoosComparison
    {A B I : Type*} [Category A] [Category B] [Category I]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (E : A ⥤ B) [E.Additive] [PreservesLimitsOfShape (Discrete ℕ) E]
    (X : I ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Z : I ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ) (e : ℕ)
    (β : ∀ P, (X.obj P).asFunctor ⋙ E.mapHomologicalComplex (.up ℤ) ≅
      index e ⋙ (Z.obj P).asFunctor)
    (hb : ∀ {P P'} (f : P ⟶ P') (n : ℕᵒᵖ),
      (E.mapHomologicalComplex (.up ℤ)).map
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (X.map f)).app n) ≫
            (β P').hom.app n = (β P).hom.app n ≫
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (Z.map f)).app
                ((index e).obj n)) :
    ∃ c : ∀ P, (E.mapHomologicalComplex (.up ℤ)).obj (roosP (X.obj P)) ⟶
        roosP ((complexRestriction B e).obj (Z.obj P)),
      ∃ δ : ∀ P, (E.mapHomologicalComplex (.up ℤ)).obj (roosF.obj (X.obj P)) ≅
          roosF.obj ((complexRestriction B e).obj (Z.obj P)),
        (∀ P (n : ℕ), c P ≫ Pi.π _ n =
          (E.mapHomologicalComplex (.up ℤ)).map
            (Pi.π (fun k : ℕ ↦ (X.obj P).asFunctor.obj (op k)) n) ≫
              (β P).hom.app (op n)) ∧
        (∀ P (p : ℤ), (δ P).hom.f (p + 1) ≫
          (roosχ ((complexRestriction B e).obj (Z.obj P)) p).hom =
            biprod.lift
              (E.map ((roosχ (X.obj P) p).hom ≫ biprod.fst) ≫ (c P).f p)
              (E.map ((roosχ (X.obj P) p).hom ≫ biprod.snd) ≫ (c P).f (p + 1))) ∧
        (∀ {P P'} (f : P ⟶ P'),
          (E.mapHomologicalComplex (.up ℤ)).map (roosF.map (X.map f)) ≫
            (δ P').hom = (δ P).hom ≫
              roosF.map ((complexRestriction B e).map (Z.map f))) := by
  let G := E.mapHomologicalComplex (.up ℤ)
  let Y P := (complexRestriction B e).obj (Z.obj P)
  let b P := transposeIso E (X.obj P) (Y P) (β P)
  let c P := piComparison G (fun n : ℕ ↦ (X.obj P).asFunctor.obj (op n)) ≫
    roosPmap (b P).hom
  let δ P := actualRoosPost E (X.obj P) (Y P) (b P)
  refine ⟨c, δ, ?_, ?_, ?_⟩
  · intro P n
    dsimp only [c, roosPmap]
    erw [Category.assoc, Pi.map_π, piComparison_comp_π_assoc]
    congr 1
    ext i : 1
    exact transposeIso_hom_f_app E (X.obj P) (Y P) (β P) i (op n)
  · intro P p
    exact actualRoosPost_coordinates E (X.obj P) (Y P) (b P) p
  · intro P P' f
    have h : (roosTowerMap E).map (X.map f) ≫ (b P').hom =
        (b P).hom ≫ (complexRestriction B e).map (Z.map f) :=
      transposeIso_natural E (X := X.obj P) (X' := X.obj P')
        (Y := Y P) (Y' := Y P') (β P) (β P') (X.map f)
          ((complexRestriction B e).map (Z.map f)) (hb f)
    exact actualRoosPost_natural E (b P) (b P') (X.map f)
      ((complexRestriction B e).map (Z.map f)) h

attribute [local irreducible] roosF roosConeFunctor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Finite free scalar extension gives the balanced comparison of strict quotient
Roos complexes, natural before localization.

Source: Stacks Project, sites-cohomology.tex, Tags 06YT and 0941; the explicit
finite-basis, balancing and arithmetic calculations in steps 1--5 of
lem-pur-finite-free-completion-exchange
(blueprint: lem-pur-finite-free-quotient-roos-comparison).

Proof: After restriction of scalars, scalar extension is tensor with the underlying
finite free R-module S, hence a finite direct sum of the identity. Faithful exact
forgetting detects exactness and invertibility of its canonical countable-product
comparison. The equality φ(t)^n = u^n v^(en), with u^n invertible, identifies
the cokernels of multiplication by these sections after extension. Balancing gives
β_n on pure local tensors, and the inverse sends a quotient lift s to 1 tensor s;
changing the lift by v^(en) changes the tensor by zero. These formulas commute with
restrictions, differentials, quotient transitions, and maps of the input complex.
Apply the additive Roos comparison to the canonical product comparison followed
by β; its two cone coordinates are exactly the displayed formula for δ. The
selection/block square gives a, which is a quasi-isomorphism by arithmetic
restriction and exact products. Its two coordinates are the selection and block
maps, and their formulas give naturality. The construction also works in rank
zero; positive e ensures that the arithmetic subsequence is cofinal. -/
theorem finiteFreeQuotientRoosComparison
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (he : 1 ≤ e)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))] :
    Nonempty (QuotientRoosExchange F t vS e) := by
  classical
  obtain ⟨hl, hc, hp⟩ := scalarExactProducts F hfree
  let := hl
  let := hc
  let := hp
  let G := F.E.mapHomologicalComplex (.up ℤ)
  obtain ⟨β, hβ⟩ := balancedTower F t vS uS hu e he hrelation
  have hb {P P'} (f : P ⟶ P') (n : ℕᵒᵖ) :
      G.map ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((quotientTower R t).map f)).app n) ≫ (β P').hom.app n =
      (β P).hom.app n ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          ((quotientTower S vS).map (G.map f))).app ((index e).obj n) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      have : Epi (quotientMap R t P n.unop) :=
        HomologicalComplex.epi_of_epi_f _ (fun i ↦ quotient_epi R t P n.unop i)
      have : Epi (G.map (quotientMap R t P n.unop)) := inferInstance
      apply (cancel_epi (G.map (quotientMap R t P n.unop))).1
      have hR := quotient_natural R t f n.unop
      have hS := quotient_natural S vS (G.map f) (e * (n.unop + 1) - 1)
      rw [← Category.assoc, ← G.map_comp, ← hR, G.map_comp,
        Category.assoc, hβ P' n.unop, ← Category.assoc, hβ P n.unop]
      exact hS
  obtain ⟨c, δ, hprod, hcone, hnat⟩ :=
    towerRoosComparison F.E (quotientTower R t) (G ⋙ quotientTower S vS) e β hb
  obtain ⟨a, ha, hac, han⟩ := arithmeticRoos (A := Modules S) e he
  refine ⟨{
    exact_limits := hl
    exact_colimits := hc
    β := β
    c := c
    product_formula := hprod
    quotient_formula := hβ
    δ := fun P ↦ by
      dsimp only [quotientRoos, Functor.comp_obj]
      exact δ P
    cone_formula := hcone
    a := fun P ↦ by
      dsimp only [quotientRoos, Functor.comp_obj]
      exact a ((quotientTower S vS).obj (G.obj P))
    arithmetic_quasiIso := fun P ↦ ha _
    arithmetic_formula := fun P p ↦ hac _ p
    delta_natural := hnat
    arithmetic_natural := fun f ↦ han ((quotientTower S vS).map (G.map f)) }⟩
end CategoryTheory.PrincipalQuotientCompletion
