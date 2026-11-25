/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# The functorial completed-coefficient derived inverse limit

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1242;
Stacks Tags 08TC, 079P and 0BK7 (blueprint: prop-weil-pbc-rlim-functoriality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Strict module towers have K-injective resolutions in the unrestricted module category.
Source: Stacks Tags 079B and 079Q (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: the strict tower category is Grothendieck abelian by the adic datum's diagram
category theorem after small-site transport. Grothendieck abelian categories have
K-injective resolutions. Transport back preserves quasi-isomorphisms and homotopies. -/
@[instance]
theorem completedTowers_hasKInjectiveResolutions (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    Abelian.HasKInjectiveResolutions (pbcTowers T R) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  have : IsGrothendieckAbelian.{u + 1} (pbcTowers T R) :=
    reductionTower_isGrothendieckAbelian T ((adicLisseForget T).obj R)
  infer_instance

/-- The limit functor on strict module towers is additive.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: a map between limits is determined by its composites with the projections.
Both addition and the limit maps have their specified component maps, giving the equality. -/
@[instance]
theorem completedTowerLimit_additive (T : Scheme.{u}) :
    (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d)).Additive := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact Functor.additive_of_preserves_binary_products _

/-- Derived strict inverse limit, computed from the actual inverse-limit functor.
Source: Stacks Tag 099N (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerRlim (T : Scheme.{u}) :
    DerivedCategory (pbcTowers T (pbcAdicCompletion T d)) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
    pbcModules T (pbcAdicCompletion T d)).rightDerivedFunctor

/-- Constant strict towers, with all transitions equal to the identity.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedTowerConstant (T : Scheme.{u}) :=
  (Functor.const ℕᵒᵖ : pbcModules T (pbcAdicCompletion T d) ⥤
    pbcTowers T (pbcAdicCompletion T d))

/-- Constant towers are additive and exact, since tower exactness is levelwise.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: all evaluations of the constant functor are the identity functor. Kernels,
cokernels and addition are computed at each level, proving the three assertions. -/
theorem completedTowerConstant_exact (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive ∧
    PreservesFiniteLimits (completedTowerConstant d T) ∧
    PreservesFiniteColimits (completedTowerConstant d T) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  exact ⟨Functor.additive_of_preserves_binary_products _, inferInstance, inferInstance⟩

/-- Additivity of the specified constant tower functor.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_additive (T : Scheme.{u}) :
    (completedTowerConstant d T).Additive := (completedTowerConstant_exact d T).1

/-- Exactness on kernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteLimits (T : Scheme.{u}) :
    PreservesFiniteLimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.1

/-- Exactness on cokernels for constant towers.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
instance completedTowerConstant_finiteColimits (T : Scheme.{u}) :
    PreservesFiniteColimits (completedTowerConstant d T) :=
  (completedTowerConstant_exact d T).2.2

/-- Constant towers on derived objects by exact termwise descent.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
abbrev completedDerivedConstant (T : Scheme.{u}) :=
  (completedTowerConstant d T).mapDerivedCategory

/-- The ordinary unit into the limit of a constant tower, with identity components.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedConstantLimitUnit (T : Scheme.{u}) :
    𝟭 (pbcModules T (pbcAdicCompletion T d)) ⟶
      completedTowerConstant d T ⋙ lim :=
  (constLimAdj : completedTowerConstant d T ⊣ lim).unit

/-- The derived unit is uniquely determined by the ordinary unit and the universal
right-derived comparison, on every representative, rather than by a cone choice.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality).
Proof: apply the right-derived unit to the constant tower of each complex after the
ordinary constant-limit unit. Naturality holds on chain maps and homotopies. Since
constant towers preserve quasi-isomorphisms, localization gives the displayed unit.
Essential surjectivity of localization and naturality give its uniqueness. -/
theorem completedConstantRlimUnit_exists (T : Scheme.{u}) :
    ∃! η : 𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
        completedDerivedConstant d T ⋙ completedTowerRlim d T,
      ∀ C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ,
        η.app (DerivedCategory.Q.obj C) =
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (completedConstantLimitUnit d T)
              (.up ℤ)).app C) ≫
          (lim : pbcTowers T (pbcAdicCompletion T d) ⥤
            pbcModules T (pbcAdicCompletion T d)).rightDerivedFunctorUnitQ
              (((completedTowerConstant d T).mapHomologicalComplex (.up ℤ)).obj C) ≫
          (completedTowerRlim d T).map
            (((completedTowerConstant d T).mapDerivedCategoryFactors).inv.app C) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  let Δ := completedTowerConstant d T
  let L : pbcTowers T (pbcAdicCompletion T d) ⥤
      pbcModules T (pbcAdicCompletion T d) := lim
  let Q : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) := DerivedCategory.Q
  let ε : L.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ L.rightDerivedFunctor :=
    { app := L.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ L.rightDerivedFunctorUnitQ_naturality f }
  let τ : Q ⟶ Q ⋙ (completedDerivedConstant d T ⋙ completedTowerRlim d T) :=
    Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (completedConstantLimitUnit d T) (.up ℤ))
        DerivedCategory.Q ≫
      Functor.whiskerLeft (Δ.mapHomologicalComplex (.up ℤ)) ε ≫
      Functor.whiskerRight Δ.mapDerivedCategoryFactors.inv (completedTowerRlim d T)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ))
    (DerivedCategory (pbcModules T (pbcAdicCompletion T d)))
  let η : 𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
      completedDerivedConstant d T ⋙ completedTowerRlim d T :=
    ff.preimage (X := 𝟭 _) (Y := completedDerivedConstant d T ⋙ completedTowerRlim d T) τ
  have hη : Functor.whiskerLeft Q η = τ := ff.map_preimage (X := 𝟭 _)
      (Y := completedDerivedConstant d T ⋙ completedTowerRlim d T) τ
  refine ⟨η, ?_, ?_⟩
  · intro C
    exact NatTrans.congr_app hη C
  · intro η' hη'
    apply Localization.natTrans_ext Q
      (HomologicalComplex.quasiIso (pbcModules T (pbcAdicCompletion T d)) (.up ℤ))
    intro C
    exact (hη' C).trans (NatTrans.congr_app hη C).symm

/-- The canonical map K → Rlim ΔK, defined by its unique representative normalization.
Source: blueprint order 1242 (blueprint: prop-weil-pbc-rlim-functoriality). -/
def completedConstantRlimUnit (T : Scheme.{u}) :
    𝟭 (DerivedCategory (pbcModules T (pbcAdicCompletion T d))) ⟶
      completedDerivedConstant d T ⋙ completedTowerRlim d T :=
  (completedConstantRlimUnit_exists d T).exists.choose

end AlgebraicGeometry.Scheme
