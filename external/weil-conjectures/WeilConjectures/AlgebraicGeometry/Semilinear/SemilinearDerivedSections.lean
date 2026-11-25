/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearTensorBase
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
public import WeilConjectures.AlgebraicGeometry.Geometry.SemilinearGeometryOps
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearSystemsExistence
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOperationsExistence

/-! # Ordinary derived semilinear sections

The categories below are module sheaves on the actual vertical sequence site and their
ordinary unbounded derived categories. All comparisons have specified sources, targets
and equations; there are no free proposition-valued parameters.

## Main definitions and statements

- `Systems`, `DS`: strict semilinear systems and their ordinary derived category.
- `Data`, `Geometry`, `OpenSystems`: the coefficient, geometric and localized calculus.
- `TensorComparisonModel`, `InverseTensorPure`: representative and pure-tensor normalization.
- `semilinearDerivedSections`: existence of the complete ordinary-derived calculus.
- `evaluation_mate`: compatibility of specified adjunction transposes with evaluation.

## References

* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1, Lemma 4.10 and Proposition 4.17
* Stacks Project, Tags 0941, 079P, 06YS, 06YY, 07A4, 07A6 and 08J7--08JB
* Zheng 4.1 and 4.10
* Stacks 06YY, 07A4, 08J7--08JB
* Zheng 4.10
* Zheng, Construction 4.1, Lemma 4.10 and Proposition 4.17
* Stacks 079P, 06YS, 06YY, 07A4, 07A6, 08J7--08JB
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r c₂ v₂ k

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

/-- All operations of the ordinary-derived semilinear system statement, on its
actual categories and with their specified maps and equations. -/
structure SemilinearDerivedSectionsData where
  /-- The actual abelian/derived system calculus. -/
  systems : Data.{c, v, r} J B τ
  /-- The specified cartesian internal-Hom reduction formula. -/
  homTransition : systems.HomReductionFormula J B τ
  /-- The signed K-flat unit, symmetry and associator belong to the same system calculus. -/
  tensorNormalization : Nonempty { M : NormalizedTensorModel.{c, v, r}
    (coefficientSequenceTopology J) (systemRing.{c, v, max c v r} J B τ) //
      M.closed = systems.closed }
  /-- A morphism of topoi induces the actual geometric system operations. -/
  geometric : ∀ {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush) [PreservesFiniteLimits uInv],
    {G : Geometry.{c, v, r} J B τ systems J' uInv uPush adjSet //
      G.TransitionFormula J B τ systems J' uInv uPush adjSet ∧
      G.PullTransitionFormula J B τ systems J' uInv uPush adjSet ∧
      G.ProjectionEvaluation J B τ systems J' uInv uPush adjSet}
  /-- Compatible coefficient-system maps have the stated scalar-extension calculus. -/
  coefficientExtension : ∀ (F : ℕ → Sheaf J CommRingCat.{max c v r})
    (σ : ∀ n : ℕ, F (n + 1) ⟶ F n) (α : ∀ n : ℕ, B n ⟶ F n)
    (hα : ∀ n : ℕ, α (n + 1) ≫ σ n = τ n ≫ α n),
    ScalarSystems.{c, v, r} J B τ F σ α hα
  /-- Exact open-localization operations with the actual normalized level adjunctions. -/
  localization : ∀ U : C, OpenSystems.{c, v, r} J B τ U

end WeilConjectures.SemilinearSections

namespace WeilConjectures.SemilinearSections
section CategoricalEvaluation

variable {X Y Z W x y z w : Type k}
  [Category.{k} X] [Category.{k} Y] [Category.{k} Z] [Category.{k} W]
  [Category.{k} x] [Category.{k} y] [Category.{k} z] [Category.{k} w]

/-- A pair of evaluation comparisons normalized by both adjunction identities.
This categorical helper is applied to the actual system and level categories above. -/
structure AdjunctionEvaluation (E : X ⥤ x) (F : Y ⥤ y)
    {L : X ⥤ Y} {R : Y ⥤ X} (adj : L ⊣ R)
    {l : x ⥤ y} {r : y ⥤ x} (level : l ⊣ r) where
  /-- Evaluation of the left adjoint. -/
  left : L ⋙ F ≅ E ⋙ l
  /-- Evaluation of the right adjoint. -/
  right : R ⋙ E ≅ F ⋙ r
  /-- Unit evaluation. -/
  unit : ∀ A : X,
    E.map (adj.unit.app A) ≫ right.hom.app (L.obj A) ≫
      r.map (left.hom.app A) = level.unit.app (E.obj A)
  /-- Counit evaluation. -/
  counit : ∀ B : Y,
    l.map (right.hom.app B) ≫ level.counit.app (F.obj B) =
      left.inv.app (R.obj B) ≫ F.map (adj.counit.app B)

/-- Evaluation commutes with the specified ordinary adjunction-mate word.
It applies also to the open adjunction and to adjunctions formed by composition,
so the existing mate-pasting identities include proper direct-image composition. -/
theorem evaluation_mate
    {E₁ : X ⥤ x} {F₁ : Y ⥤ y} {E₂ : Z ⥤ z} {F₂ : W ⥤ w}
    {L₁ : X ⥤ Y} {R₁ : Y ⥤ X} {L₂ : Z ⥤ W} {R₂ : W ⥤ Z}
    {l₁ : x ⥤ y} {r₁ : y ⥤ x} {l₂ : z ⥤ w} {r₂ : w ⥤ z}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (level₁ : l₁ ⊣ r₁) (level₂ : l₂ ⊣ r₂)
    (A₁ : AdjunctionEvaluation E₁ F₁ adj₁ level₁)
    (A₂ : AdjunctionEvaluation E₂ F₂ adj₂ level₂)
    {G : X ⥤ Z} {H : Y ⥤ W} {g : x ⥤ z} {h : y ⥤ w}
    (γ : G ⋙ E₂ ≅ E₁ ⋙ g) (η : H ⋙ F₂ ≅ F₁ ⋙ h)
    (α : TwoSquare G L₁ L₂ H) (a : TwoSquare g l₁ l₂ h)
    (compatible : ∀ A : X,
      F₂.map (α.app A) ≫ η.hom.app (L₁.obj A) ≫ h.map (A₁.left.hom.app A) =
        A₂.left.hom.app (G.obj A) ≫ l₂.map (γ.hom.app A) ≫ a.app (E₁.obj A)) :
    ∀ B : Y,
      E₂.map ((mateEquiv adj₁ adj₂ α).app B) ≫ A₂.right.hom.app (H.obj B) ≫
          r₂.map (η.hom.app B) =
        γ.hom.app (R₁.obj B) ≫ g.map (A₁.right.hom.app B) ≫
          (mateEquiv level₁ level₂ a).app (F₁.obj B) := by
  intro B
  apply (level₂.homEquiv _ _).symm.injective
  change l₂.map _ ≫ level₂.counit.app _ = l₂.map _ ≫ level₂.counit.app _
  simp only [Functor.map_comp, Category.assoc]
  apply (cancel_epi (A₂.left.hom.app (G.obj (R₁.obj B)))).1
  have hleft := A₂.left.hom.naturality ((mateEquiv adj₁ adj₂ α).app B)
  dsimp only [Functor.comp_map] at hleft
  rw [← reassoc_of% hleft]
  have hcounit := level₂.counit.naturality (η.hom.app B)
  dsimp only [Functor.comp_map, Functor.id_map] at hcounit
  rw [hcounit]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% (A₂.counit (H.obj B))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← F₂.map_comp_assoc, mateEquiv_counit]
  rw [F₂.map_comp, Category.assoc]
  have hη := η.hom.naturality (adj₁.counit.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hη
  rw [hη]
  rw [mateEquiv_counit]
  have ha := a.naturality (A₁.right.hom.app B)
  dsimp only [Functor.comp_map, Functor.comp_obj] at ha
  rw [reassoc_of% ha]
  rw [← reassoc_of% (compatible (R₁.obj B))]
  rw [← h.map_comp, A₁.counit]
  rw [← h.map_comp, Iso.hom_inv_id_app_assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem evaluation_transpose
    {E : X ⥤ x} {F : Y ⥤ y} {L : X ⥤ Y} {R : Y ⥤ X}
    {l : x ⥤ y} {r : y ⥤ x} (adj : L ⊣ R) (level : l ⊣ r)
    (A : AdjunctionEvaluation E F adj level) {P : X} {Q : Y} (f : L.obj P ⟶ Q) :
    E.map ((adj.homEquiv _ _) f) ≫ A.right.hom.app Q =
      (level.homEquiv _ _) (A.left.inv.app P ≫ F.map f) := by
  rw [adj.homEquiv_unit, level.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hr := A.right.hom.naturality f
  dsimp only [Functor.comp_map] at hr
  rw [hr]
  have hu' : E.map (adj.unit.app P) ≫ A.right.hom.app (L.obj P) =
      level.unit.app (E.obj P) ≫ r.map (A.left.inv.app P) := by
    rw [← A.unit P]
    have hi := (r.mapIso (A.left.app P)).hom_inv_id
    change r.map (A.left.hom.app P) ≫ r.map (A.left.inv.app P) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  rw [← Category.assoc, hu', Category.assoc]

end CategoricalEvaluation
end WeilConjectures.SemilinearSections

namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [ambientSmall : EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem reduction_naturality {m n : ℕ} (h : n ≤ m)
    (S : ScalarData.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h))
    {M N : DS.{c, v, max c v r} J B τ} (f : M ⟶ N) :
    S.T.map ((e.{c, v, max c v r} J B τ m).map f) ≫
        reduction.{c, v, max c v r} J B τ h S N =
      reduction.{c, v, max c v r} J B τ h S M ≫
        (e.{c, v, max c v r} J B τ n).map f := by
  apply (S.adjunction.homEquiv _ _).injective
  rw [S.adjunction.homEquiv_naturality_left,
    S.adjunction.homEquiv_naturality_right]
  simp only [reduction, Equiv.apply_symm_apply]
  exact (derivedTransition.{c, v, max c v r} J B τ h).naturality f

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem push_transition_of_pull (A : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)
    (hp : G.PullTransitionFormula J B τ A J' uInv uPush adjSet) :
    G.TransitionFormula J B τ A J' uInv uPush adjSet := by
  intro m n h N
  let V := derivedExact.{c, v, max c v r, c, v} J J' (B n)
    (G.coefficients n) (G.inverseImage n).modules
  let S := (G.target.scalar h).T
  let P := G.push.rightDerivedFunctor.obj N
  have hr :
      V.map (reduction.{c, v, max c v r} J B τ h (A.scalar h) P) ≫
          (G.pullEvaluation n).inv.app P =
        (G.coefficientPullback h).hom.app ((e.{c, v, max c v r} J B τ m).obj P) ≫
          S.map ((G.pullEvaluation m).inv.app P) ≫
            reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h
              (G.target.scalar h)
              (G.pull.mapDerivedCategory.obj P) := by
    apply (cancel_epi
      (S.map ((G.pullEvaluation m).hom.app P) ≫
        (G.coefficientPullback h).inv.app ((e.{c, v, max c v r} J B τ m).obj P))).1
    simp only [Category.assoc]
    rw [← reassoc_of% (hp h P)]
    simp only [Iso.inv_hom_id_app_assoc]
    have hi := (S.mapIso ((G.pullEvaluation m).app P)).hom_inv_id
    change S.map ((G.pullEvaluation m).hom.app P) ≫
      S.map ((G.pullEvaluation m).inv.app P) = 𝟙 _ at hi
    simp only [← Category.assoc, hi, Category.id_comp]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  apply ((G.derivedLevelAdjunction n).homEquiv _ _).symm.injective
  change V.map _ ≫ (G.derivedLevelAdjunction n).counit.app _ =
    V.map _ ≫ (G.derivedLevelAdjunction n).counit.app _
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [V]
  rw [G.counit_evaluation n N]
  rw [reassoc_of% hr]
  have hn := reduction_naturality.{c, v, r} J' G.coefficients G.coefficientTransition
    h (G.target.scalar h) (G.adjunction.counit.app N)
  dsimp only [Functor.comp_obj] at hn
  dsimp only [P]
  erw [← hn]
  rw [← S.map_comp_assoc, ← G.counit_evaluation m N, S.map_comp]
  have hq := (G.coefficientPullback h).hom.naturality
    ((G.pushEvaluation m).hom.app N)
  dsimp only [Functor.comp_map] at hq
  simp only [Category.assoc]
  rw [← reassoc_of% hq]
  have hc := (G.derivedLevelAdjunction n).counit.naturality
    (reduction.{c, v, max c v r} J' G.coefficients G.coefficientTransition h (G.target.scalar h) N)
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  dsimp only [Geometry.coefficientMate]
  rw [reassoc_of% (mateEquiv_counit (G.derivedLevelAdjunction m)
    (G.derivedLevelAdjunction n) (TwoSquare.mk _ _ _ _ (G.coefficientPullback h).hom)
      ((e.{c, v, max c v r} J' G.coefficients G.coefficientTransition m).obj N))]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
private theorem projection_evaluation (A : Data.{c, v, r} J B τ)
    {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
    (J' : GrothendieckTopology C')
    (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
    (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
    (adjSet : uInv ⊣ uPush)
    (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet) :
    G.ProjectionEvaluation J B τ A J' uInv uPush adjSet := by
  intro n N P
  let V := derivedExact.{c, v, max c v r, c, v} J J' (B n)
    (G.coefficients n) (G.inverseImage n).modules
  let s := (G.target.levelClosed n).tensor
  let E := e.{c, v, max c v r} J B τ n
  let F := e.{c, v, max c v r} J' G.coefficients G.coefficientTransition n
  let ev : AdjunctionEvaluation E F G.adjunction (G.derivedLevelAdjunction n) :=
    { left := G.pullEvaluation n
      right := G.pushEvaluation n
      unit := G.unit_evaluation n
      counit := G.counit_evaluation n }
  rw [Geometry.tensorProjection]
  rw [reassoc_of% (evaluation_transpose G.adjunction (G.derivedLevelAdjunction n) ev _)]
  rw [← (G.derivedLevelAdjunction n).homEquiv_naturality_right]
  simp only [Geometry.levelTensorProjection, ← Category.assoc]
  erw [← (G.derivedLevelAdjunction n).homEquiv_naturality_left
    ((A.tensorEvaluation n).hom.app (G.push.rightDerivedFunctor.obj N, P) ≫
      (A.levelClosed n).tensor.map
        (Prod.mkHom ((G.pushEvaluation n).hom.app N) (𝟙 ((e J B τ n).obj P))))]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hn := (G.target.tensorEvaluation n).hom.naturality
    (Prod.mkHom (G.adjunction.counit.app N) (𝟙 (G.pull.mapDerivedCategory.obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  have hc : F.map (G.adjunction.counit.app N) =
      (G.pullEvaluation n).hom.app (G.push.rightDerivedFunctor.obj N) ≫
        V.map ((G.pushEvaluation n).hom.app N) ≫
          (G.derivedLevelAdjunction n).counit.app (F.obj N) := by
    dsimp only [F, V]
    rw [G.counit_evaluation n N]
    simp only [Iso.hom_inv_id_app_assoc]
  have hm :
      s.map (Prod.mkHom (F.map (G.adjunction.counit.app N))
          (F.map (𝟙 (G.pull.mapDerivedCategory.obj P)))) ≫
        s.map (Prod.mkHom (𝟙 (F.obj N)) ((G.pullEvaluation n).hom.app P)) =
      s.map (Prod.mkHom
          ((G.pullEvaluation n).hom.app (G.push.rightDerivedFunctor.obj N))
          ((G.pullEvaluation n).hom.app P)) ≫
        s.map (Prod.mkHom (V.map ((G.pushEvaluation n).hom.app N)) (𝟙 _)) ≫
          s.map (Prod.mkHom
            ((G.derivedLevelAdjunction n).counit.app (F.obj N)) (𝟙 _)) := by
    simp only [← s.map_comp]
    congr 1
    ext <;> simp [hc]
  dsimp only [F, s, V] at hm
  rw [hm]
  rw [reassoc_of% (G.tensorPullback_evaluation n (G.push.rightDerivedFunctor.obj N) P)]
  dsimp only [ev]
  simp only [Iso.inv_hom_id_app_assoc]
  have hl := (G.levelTensorPullback n).hom.naturality
    (Prod.mkHom ((G.pushEvaluation n).hom.app N) (𝟙 ((e J B τ n).obj P)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hl
  rw [reassoc_of% hl]
  simp only [CategoryTheory.Functor.map_id]
  rfl

/-- Ordinary derived semilinear sections and their coefficient-linear operations. -/
theorem semilinearDerivedSections :
    Nonempty (SemilinearDerivedSectionsData.{c, v, r} J B τ) := by
  let S := (semilinearSystemData.{c, v, r} J B τ).some
  let O := (semilinearOperationsData.{c, v, r} J B τ S.systems).some
  exact ⟨{
    systems := S.systems
    homTransition := S.homTransition
    tensorNormalization := S.tensorNormalization
    geometric := by
      intro C' cat small J' uInv uPush adjSet hlim
      obtain ⟨G, hG⟩ := O.geometric J' uInv uPush adjSet
      exact ⟨G, push_transition_of_pull J B τ S.systems J' uInv uPush adjSet G hG,
        hG, projection_evaluation J B τ S.systems J' uInv uPush adjSet G⟩
    coefficientExtension := O.coefficientExtension
    localization := O.localization
  }⟩

end WeilConjectures.SemilinearSections
