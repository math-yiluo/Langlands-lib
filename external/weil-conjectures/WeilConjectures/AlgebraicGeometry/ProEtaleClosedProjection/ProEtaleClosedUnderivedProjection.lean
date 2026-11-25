/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedCounit
import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Underived projection for a closed pro-etale immersion

## References

* Stacks Project, Tags 09AA and 09AH, Section 03EK and Tag 03EL
* Stacks, Tags 03D2, 03D3 and 09AA
* Stacks, Section 03EK
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ProEtaleClosedProjection

/-- The actual module adjunction is uniquely characterized by its constructed unit
on every section. This fixes adjunction data, rather than choosing an arbitrary
adjunction between the functors. -/
theorem adjunction_exists {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    ∃! ai : inverse i R ⊣ proEtaleRingedDirectImage i R,
      ∀ (F : Modules R) (V : X.ProEt) (s : F.val.obj (op V)),
        (ai.unit.app F).val.app (op V) s = inverseSection i F V s := by
  refine ⟨AlgebraicGeometry.Scheme.canonicalAdjunction i R, ?_, ?_⟩
  · intro F V s
    exact AlgebraicGeometry.Scheme.canonicalUnit_sections i R F (op V) s
  · intro ai hai
    apply Adjunction.ext
    ext F V s
    exact (hai F V.unop s).trans
      (AlgebraicGeometry.Scheme.canonicalUnit_sections i R F V s).symm

/-- The canonical module adjunction, selected from the unique unit-normalized
characterization. Its data are determined by the actual inverse-image section map. -/
noncomputable def adjunction {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X) :
    inverse i R ⊣ proEtaleRingedDirectImage i R :=
  Classical.choose (adjunction_exists i R)

/-- The projection map is the specified adjunct of the normalized tensor comparison
followed by the counit on the first factor. No isomorphism or arbitrary map is chosen. -/
noncomputable def projection {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) :
    tensor ((proEtaleRingedDirectImage i R).obj M) F ⟶
      (proEtaleRingedDirectImage i R).obj (tensor M ((inverse i R).obj F)) :=
  ((adjunction i R).homEquiv _ _)
    (comparison i R ((proEtaleRingedDirectImage i R).obj M) F ≫
      tensorMap ((adjunction i R).counit.app M) (𝟙 ((inverse i R).obj F)))

/-- The ring sheaf B regarded as an R-module through the given ring morphism. -/
noncomputable abbrev coefficientModule {X : Scheme.{u}} {R B : Rings X} (a : R ⟶ B) :
    Modules R :=
  (restrict a).obj (SheafOfModules.unit (proEtaleModuleCoefficients B))

private noncomputable def regularInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    (B : Rings X) : (inverse i B).obj (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≅
      SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B)) := by
  let : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : Z.ProEt ⥤ proEtaleSiteModel Z).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{u, u + 1, u + 1} (C := Z.ProEt)).functor.IsEquivalence
  have : PreservesFiniteLimits (proEtaleModelBaseChange i) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  have : (proEtaleModelBaseChange i).Final := inferInstance
  exact (proEtaleModuleFromModel _).mapIso
    (asIso (SheafOfModules.pullbackObjUnitToUnit (proEtaleModelRingUnit i B)))

private theorem regularInverseIso_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    (B : Rings X) (V : X.ProEt) (b : B.obj.obj (op V)) :
    (regularInverseIso i B).hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (SheafOfModules.unit (proEtaleModuleCoefficients B)) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b := by
  let φ := proEtaleModelRingUnit i B
  have h := ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).apply_symm_apply
    (SheafOfModules.unitToPushforwardObjUnit φ)
  have h' := congrArg (fun k ↦ k.val.app (op (AsSmall.up.obj V)) b) h
  change _ = _ at h'
  exact h'

attribute [local irreducible] regularInverseIso proEtaleModuleInverseImage
  inverseSection scalarIdentification

private noncomputable def coefficientInverseIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) :
    (inverse i R).obj (coefficientModule a) ≅
      (restrict (inverseRingMap i a)).obj
        (SheafOfModules.unit (proEtaleModuleCoefficients (inverseRing i B))) :=
  scalarIdentification i a (SheafOfModules.unit (proEtaleModuleCoefficients B)) ≪≫
    (restrict (inverseRingMap i a)).mapIso (regularInverseIso i B)

private theorem coefficientInverseIso_sections {X Z : Scheme.{u}} (i : Z ⟶ X)
    {R B : Rings X} (a : R ⟶ B) (V : X.ProEt) (b : B.obj.obj (op V)) :
    (coefficientInverseIso i a).hom.val.app (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app B).hom.app (op V) b := by
  have h : (scalarIdentification i a
      (SheafOfModules.unit (proEtaleModuleCoefficients B))).hom.val.app
        (op ((proEtaleBaseChange i).obj V))
        (inverseSection i (coefficientModule a) V b) =
      inverseSection i (SheafOfModules.unit (proEtaleModuleCoefficients B)) V b := by
    unfold scalarIdentification
    exact (Classical.choose_spec
      (scalarIdentification_exists i a (SheafOfModules.unit
        (proEtaleModuleCoefficients B)))).1 V b
  unfold coefficientInverseIso
  change (regularInverseIso i B).hom.val.app (op ((proEtaleBaseChange i).obj V))
    ((scalarIdentification i a (SheafOfModules.unit (proEtaleModuleCoefficients B))).hom.val.app
      (op ((proEtaleBaseChange i).obj V))
      (inverseSection i (coefficientModule a) V b)) = _
  exact (congrArg ((regularInverseIso i B).hom.val.app
    (op ((proEtaleBaseChange i).obj V))) h).trans (regularInverseIso_sections i B V b)

attribute [local irreducible] coefficientInverseIso

private noncomputable abbrev coefficientMap {X : Scheme.{u}} {R B : Rings X}
    (a : R ⟶ B) : proEtaleModuleCoefficients R ⟶ proEtaleModuleCoefficients B :=
  (sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a

section
universe s h
variable {C : Type s} [Category.{h} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
  {R₀ B₀ : Sheaf J RingCat.{u + 1}}

end

private theorem tensorSecond_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    SheafOfModules.siteSheafTensorSecondMap M (𝟙 N) = 𝟙 (tensor M N) := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = 𝟙 _
  rw [← S.map_id]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorSecond_comp {X : Scheme.{u}} {R : Rings X}
    (M : Modules R) {N N' N'' : Modules R} (b : N ⟶ N') (c : N' ⟶ N'') :
    SheafOfModules.siteSheafTensorSecondMap M (b ≫ c) =
      SheafOfModules.siteSheafTensorSecondMap M b ≫
        SheafOfModules.siteSheafTensorSecondMap M c := by
  let S := PresheafOfModules.sheafification.{u + 1} (𝟙 (proEtaleModuleCoefficients R).obj)
  change S.map _ = S.map _ ≫ S.map _
  rw [← S.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private theorem tensorMap_id {X : Scheme.{u}} {R : Rings X} (M N : Modules R) :
    tensorMap (𝟙 M) (𝟙 N) = 𝟙 (tensor M N) := by
  unfold tensorMap
  rw [tensorSecond_id, Category.comp_id]
  exact (SheafOfModules.siteSheafTensorRight N).map_id M

private theorem tensorMap_comp {X : Scheme.{u}} {R : Rings X}
    {M M' M'' N N' N'' : Modules R}
    (a : M ⟶ M') (a' : M' ⟶ M'') (b : N ⟶ N') (b' : N' ⟶ N'') :
    tensorMap (a ≫ a') (b ≫ b') = tensorMap a b ≫ tensorMap a' b' := by
  simp only [tensorMap, Functor.map_comp, tensorSecond_comp, Category.assoc]
  rw [← Category.assoc (SheafOfModules.siteSheafTensorSecondMap M' b)]
  rw [← SheafOfModules.siteSheafTensorSecondMap_naturality a' b]
  simp only [Category.assoc]

private noncomputable def tensorIso {X : Scheme.{u}} {R : Rings X}
    {M M' N N' : Modules R} (e : M ≅ M') (f : N ≅ N') :
    tensor M N ≅ tensor M' N' where
  hom := tensorMap e.hom f.hom
  inv := tensorMap e.inv f.inv
  hom_inv_id := by rw [← tensorMap_comp, e.hom_inv_id, f.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [← tensorMap_comp, e.inv_hom_id, f.inv_hom_id, tensorMap_id]

private theorem tensorCounit_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (R : Rings X) (M : Modules (inverseRing i R))
    (F : Modules R) :
    IsIso (tensorMap ((adjunction i R).counit.app M) (𝟙 ((inverse i R).obj F))) := by
  have := proEtale_ringed_closed_counit i R (adjunction i R) M
  unfold tensorMap
  rw [tensorSecond_id, Category.comp_id]
  infer_instance

private theorem projection_natural {X Z : Scheme.{u}} (i : Z ⟶ X) (R : Rings X)
    (M M' : Modules (inverseRing i R)) (F F' : Modules R)
    (a : M ⟶ M') (b : F ⟶ F') :
    tensorMap ((proEtaleRingedDirectImage i R).map a) b ≫ projection i R M' F' =
      projection i R M F ≫
        (proEtaleRingedDirectImage i R).map (tensorMap a ((inverse i R).map b)) := by
  unfold projection
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have hn := (inverseImage_tensor_comparison (𝟙 Z) i R
    ((proEtaleRingedDirectImage i R).obj M) F).2.2.1
    ((proEtaleRingedDirectImage i R).obj M') F'
    ((proEtaleRingedDirectImage i R).map a) b
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← tensorMap_comp, Category.comp_id, Category.id_comp]
  congr 2
  exact (adjunction i R).counit.naturality a

private theorem projection_isIso {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ) (R : Rings X)
    (M : Modules (inverseRing i R)) (F : Modules R) : IsIso (projection i R M F) := by
  obtain ⟨_, _, ai, aj, hc, _, hz, _, _, _, _, _, hs, _⟩ :=
    proEtale_ringed_open_closed i U hU R
  let H := tensor ((proEtaleRingedDirectImage i R).obj M) F
  obtain ⟨e, _, _⟩ := SheafOfModules.exists_localizedSiteTensorRestriction.{u + 1, u, u + 1, u + 1}
    (ProEt.topology X) R U
  have hres : IsZero ((SheafOfModules.overFunctor (proEtaleModuleCoefficients R) U).obj H) :=
    ((SheafOfModules.siteSheafTensorRight (A := R.over U) (F.over U)).map_isZero
      (hz M)).of_iso (e _ _)
  have : (proEtaleRingedExtensionByZero U R).IsLeftAdjoint := aj.isLeftAdjoint
  have hleft := (proEtaleRingedExtensionByZero U R).map_isZero hres
  let T := ComposableArrows.mk₂ (aj.counit.app H) (ai.unit.app H)
  have hT : T.Exact := (hs H).2.2
  have he := (T.exact₂_iff hT.toIsComplex).1 hT
  have : Mono (ai.unit.app H) := he.mono_g (hleft.eq_of_src _ _)
  have : Epi (ai.unit.app H) := (hs H).2.1
  have : IsIso (ai.unit.app H) := isIso_of_mono_of_epi _
  have : IsIso ai.counit := by
    have := hc
    exact NatIso.isIso_of_isIso_app _
  have : (proEtaleRingedDirectImage i R).Full := ai.fullyFaithfulROfIsIsoCounit.full
  have : (proEtaleRingedDirectImage i R).Faithful := ai.fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso ((adjunction i R).unit.app H) :=
    (adjunction i R).isIso_unit_app_iff_mem_essImage.2
      ⟨(inverse i R).obj H, ⟨(asIso (ai.unit.app H)).symm⟩⟩
  have := (inverseImage_tensor_comparison (𝟙 Z) i R
    ((proEtaleRingedDirectImage i R).obj M) F).1
  have := tensorCounit_isIso i R M F
  change IsIso (((adjunction i R).homEquiv _ _) _)
  rw [Adjunction.homEquiv_unit]
  infer_instance

end AlgebraicGeometry.ProEtaleClosedProjection
