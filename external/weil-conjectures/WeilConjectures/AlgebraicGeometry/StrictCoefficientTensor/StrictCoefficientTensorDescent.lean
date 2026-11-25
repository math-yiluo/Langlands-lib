/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
import WeilConjectures.Algebra.Homology.System.SystemEvaluationTopos
import all WeilConjectures.CategoryTheory.Constant.ConstantTowerNormalization
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Descent of strict coefficient tensor complexes

Source: Stacks Project, sites-cohomology.tex, Tags 0G7D, 06YS, 06YY;
blueprint, normalized towers, reduction construction
(blueprint: lem-sp-strict-coefficient-tensor-descent).

Index zero denotes the paper's coefficient indexed by one. The target is the
ordinary derived category of module sheaves on the existing ringed sequence site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize

namespace WeilConjectures.SemilinearSections.StrictCoefficientTensor

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
  (S : ℕ → Sheaf J CommRingCat.{r}) (q : ∀ n : ℕ, S (n + 1) ⟶ S n)
  (a : ∀ n : ℕ, R ⟶ S n)

/-- The resolving class is K-flat complexes with flat terms.
Source: Stacks 06YS, 0G7D (blueprint: lem-sp-strict-coefficient-tensor-descent). -/
def Resolving (P : CochainComplex (Mod.{c, v, r} J R) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := R) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{c, v, r, r} (J := J) (R := R) (P.X i)

/-- The existing scalar-extension model at the fixed ordinary localization universes.
Source: Stacks 06YY (blueprint: lem-sp-strict-coefficient-tensor-descent). -/
abbrev Scalar {T : Sheaf J CommRingCat.{r}} (b : R ⟶ T) :=
  @SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, r,
    max c v (r + 1), max c v (r + 1)} C _ (siteSmall.{c, v, r}) J _
      (locallyBijective.{c, v, r} J) (abelianSheafify.{c, v, r} J) R T b
      (hasDerived.{c, v, r} J R) (hasDerived.{c, v, r} J T)

/-- A pure scalar-extension section, in the actual ordinary extension functor.
The target coefficient acts on the first tensor factor; symmetry gives the
paper's notation x tensor c.
Source: Stacks 03EK, 06YY (blueprint: lem-sp-strict-coefficient-tensor-descent). -/
def pure {T : Sheaf J CommRingCat.{r}} (b : R ⟶ T)
    (d : Scalar J R b)
    (M : Mod.{c, v, r} J R) (U : Cᵒᵖ) (x : M.val.obj U) (s : T.obj.obj U) :
    (d.E.obj M).val.obj U :=
  @SMul.smul ((ring J T).obj.obj U) _ inferInstance s
    ((eqToHom (d.obj_eq M).symm).val.app U (extensionUnit b M U x))

set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genCtorIdx false in
/-- The full normalized descent datum, including strict transitions before localization.
All ordinary extensions are fixed by the dependency's sheafified-tensor formulas.
The universal comparison and its uniqueness fix descent, rather than selecting
unrelated level objects or a functor by a mere existence assertion.
Source: Stacks 0G7D, 06YS, 06YY and the blueprint reduction construction
(blueprint: lem-sp-strict-coefficient-tensor-descent). -/
structure Descent where
  /-- Each level uses the recorded ordinary and derived change of rings. -/
  scalar : ∀ n : ℕ, Scalar J R (a n)
  /-- Ordinary strict tensor systems; applying this termwise gives F(P). -/
  ordinary : Mod.{c, v, r} J R ⥤ Systems.{c, v, r} J S q
  [additive : ordinary.Additive]
  /-- Its levels are the actual sheafified scalar extensions. -/
  level : ∀ n : ℕ, ordinary ⋙ evaluation.{c, v, r} J S q n ≅ (scalar n).E
  /-- Every transition, including composite indices, has the coefficient formula. -/
  transition_pure : ∀ (M : Mod.{c, v, r} J R) (m n : ℕ) (h : n ≤ m)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : (S m).obj.obj U),
    ((res (coefficientMap J S q h)).map ((level n).hom.app M)).val.app U
      (((transition J S q h).app (ordinary.obj M)).val.app U
        (((level m).inv.app M).val.app U (pure J R (a m) (scalar m) M U x s))) =
      pure J R (a n) (scalar n) M U x ((coefficientMap J S q h).hom.app U s)
  /-- The underived complex functor inverts quasi-isomorphisms on the resolving class. -/
  preserves : ∀ {P P' : CochainComplex (Mod.{c, v, r} J R) ℤ} (f : P ⟶ P'),
    Resolving J R P → Resolving J R P' → QuasiIso f →
      QuasiIso ((ordinary.mapHomologicalComplex (.up ℤ)).map f)
  /-- Descent lands in the ordinary derived category of entire strict systems. -/
  T : D.{c, v, r} J R ⥤ DS.{c, v, r} J S q
  /-- A natural comparison, before restricting to K-flat complexes. -/
  ε : DerivedCategory.Q ⋙ T ⟶ ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  /-- Everywhere-defined left derivation. -/
  pointwise : (ordinary.mapHomologicalComplex (.up ℤ) ⋙
    DerivedCategory.Q).HasPointwiseLeftDerivedFunctor
      (HomologicalComplex.quasiIso (Mod.{c, v, r} J R) (.up ℤ))
  universal : T.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (Mod.{c, v, r} J R) (.up ℤ))
  /-- Exactness in the triangulated sense. -/
  triangulated : ∃ (_ : T.CommShift ℤ), T.IsTriangulated
  computes : ∀ P : CochainComplex (Mod.{c, v, r} J R) ℤ,
    Resolving J R P → IsIso (ε.app P)
  /-- Exact evaluation identifies this descent with derived scalar extension. -/
  evaluation : ∀ n : ℕ, T ⋙ e.{c, v, r} J S q n ≅ (scalar n).T
  /-- The evaluation comparison respects the two actual computation counits. -/
  evaluation_normalized : ∀ (P : CochainComplex (Mod.{c, v, r} J R) ℤ)
    (_hP : Resolving J R P) (n : ℕ),
    (e J S q n).map (ε.app P) ≫
        (Functor.mapDerivedCategoryFactors (SemilinearSections.evaluation J S q n)).hom.app
          ((ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (level n) (.up ℤ)).hom.app P) =
      (evaluation n).hom.app (DerivedCategory.Q.obj P) ≫ (scalar n).ε.app P
  /-- Uniqueness with respect to the resolving-class normalization itself. -/
  unique : ∀ (T' : D.{c, v, r} J R ⥤ DS.{c, v, r} J S q)
    (ε' : DerivedCategory.Q ⋙ T' ⟶
      ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q),
    (∀ P : CochainComplex (Mod.{c, v, r} J R) ℤ,
      Resolving J R P → IsIso (ε'.app P)) →
    ∃! α : T ≅ T', ∀ P : CochainComplex (Mod.{c, v, r} J R) ℤ,
      Resolving J R P → α.hom.app (DerivedCategory.Q.obj P) ≫ ε'.app P = ε.app P


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def algebraSequence
    (ha : ∀ n : ℕ, a (n + 1) ≫ q n = a n) :
    (Functor.const ℕᵒᵖ).obj R ⟶ rings J S q :=
  NatTrans.ofOpSequence (fun n ↦ a n) (by
    intro n
    change 𝟙 R ≫ a n = a (n + 1) ≫ _
    simpa only [Category.id_comp, rings,
      Functor.ofOpSequence_map_homOfLE_succ] using (ha n).symm)

private def ordinaryTensor
    (ha : ∀ n : ℕ, a (n + 1) ≫ q n = a n) :
    Mod.{c, v, r} J R ⥤ Systems.{c, v, r} J S q :=
  SheafOfModules.SequenceProjection.extension R (rings J S q) (algebraSequence J R S q a ha) ⋙
    (SheafOfModules.strictSystemSequenceEquivalence (rings J S q)).functor

attribute [local irreducible] ordinaryTensor

private def scalarModel
    (ha : ∀ n : ℕ, a (n + 1) ≫ q n = a n) (n : ℕ) : Scalar J R (a n) :=
  (SheafOfModules.SequenceProjection.scalar R (rings J S q)
    (algebraSequence J R S q a ha) n).model

private theorem evaluationRingMap (n : ℕ) :
    eqToHom (evaluation_ring J S q n).symm =
      SheafOfModules.systemSequenceVerticalRingMap (rings J S q) n := by
  ext U x
  simp only [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

private def sequenceLevelIso
    (M : SheafOfModules.StrictRingSystem.{c, v, r} (rings J S q)) (n : ℕ) :
    (evaluation J S q n).obj
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J S q)).functor.obj M) ≅
        M.level n :=
  (SheafOfModules.pushforwardCongr (evaluationRingMap J S q n)).app
      ((SheafOfModules.strictSystemSequenceEquivalence (rings J S q)).functor.obj M) ≪≫
    (SheafOfModules.strictSystemSequenceUnitLevel (rings J S q) M n).symm

private def ordinaryLevel
    (ha : ∀ n : ℕ, a (n + 1) ≫ q n = a n) (n : ℕ) :
    ordinaryTensor J R S q a ha ⋙ evaluation J S q n ≅ (scalarModel J R S q a ha n).E := by
  unfold ordinaryTensor
  exact NatIso.ofComponents
    (fun M ↦ sequenceLevelIso J S q
      ((SheafOfModules.SequenceProjection.extension R (rings J S q)
        (algebraSequence J R S q a ha)).obj M) n)
    (by intros; ext U x; rfl)

private theorem sequenceTransition
    (M : SheafOfModules.StrictRingSystem.{c, v, r} (rings J S q))
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) (x : (M.level m).val.obj U) :
    ((res (coefficientMap J S q h)).map (sequenceLevelIso J S q M n).hom).val.app U
      (((transition J S q h).app
        ((SheafOfModules.strictSystemSequenceEquivalence (rings J S q)).functor.obj M)).val.app U
          ((sequenceLevelIso J S q M m).inv.val.app U x)) =
      (M.transition h).val.app U x := by
  have hh := (transition_exists J S q h).exists.choose_spec
    ((SheafOfModules.strictSystemSequenceEquivalence (rings J S q)).functor.obj M) U
  have he := congrFun (eq_of_heq hh) ((sequenceLevelIso J S q M m).inv.val.app U x)
  change (sequenceLevelIso J S q M n).hom.val.app U _ = _
  refine (congrArg ((sequenceLevelIso J S q M n).hom.val.app U) he).trans ?_
  change (M.level n).val.map (𝟙 U) ((M.transition h).val.app U x) = _
  rw [PresheafOfModules.map_id]
  rfl

attribute [local irreducible] sequenceLevelIso

attribute [local irreducible] ordinaryLevel scalarModel

end WeilConjectures.SemilinearSections.StrictCoefficientTensor
