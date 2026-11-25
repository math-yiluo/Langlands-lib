/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystem
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceLimit
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1CompletedLimitBridge
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
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # The projective-line adjunction with its canonical diagonal data supplied
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v₁ v₂ v₃ v₄ v₅
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] push exceptional coefficient line

attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions

private theorem selectNormalizedArrow
    {A : Sort v₁} {B : A → Sort v₂} {C : (a : A) → B a → Sort v₃}
    {D : (a : A) → (b : B a) → C a b → Sort v₄} {E : Sort v₅}
    {P : (a : A) → (b : B a) → (c : C a b) → D a b c → Prop}
    {Q : (a : A) → (b : B a) → (c : C a b) → D a b c → E → Prop}
    (h : ∃ a b c d, P a b c d)
    (select : ∀ a b c d, P a b c d → ∃ e, Q a b c d e) :
    ∃ e, ∃ a b c d, P a b c d ∧ Q a b c d e := by
  obtain ⟨a, b, c, d, h⟩ := h
  obtain ⟨e, he⟩ := select a b c d h
  exact ⟨e, a, b, c, d, h, he⟩

@[irreducible] private noncomputable def diagonalLocalizations (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) : DiagonalTraceLocalizations ℓ X := by
  letI : IsGrothendieckAbelian.{u + 1} (DiagonalCompleted ℓ X) :=
    SheafOfModules.isGrothendieckAbelian_coefficientUniverse _
  letI : IsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalMod ℓ X)
  letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalAb X)
  letI : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X) :=
    CategoryTheory.RingedStrictTowerProof.tower_grothendieck (DiagonalCompleted ℓ X)
  let ab := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalAb X)
  let mod := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalMod ℓ X)
  let systems := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalSystems ℓ X)
  let abSystems := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb X)
  let completed := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} (DiagonalCompleted ℓ X)
  let completedSystems := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1}
    (ℕᵒᵖ ⥤ DiagonalCompleted ℓ X)
  letI := systems
  exact ⟨ab, mod, systems, abSystems, completed, completedSystems,
    hasExt_of_hasDerivedCategory _⟩

private theorem withCanonicalData
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [DiagonalTraceLocalizations ℓ Y]
    [DiagonalTraceLocalizations ℓ (ProjectiveLine Y)]
    [DiagonalTraceLocalizations ℓ (diagonalSurface Y)]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    {P : Prop}
    (finish : ∀ (hY : IsUnit (ℓ : Γ(Y, ⊤)))
      (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
      (_hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
      (_hsystem : DiagonalCycleSystemSpec ℓ Y hY D)
      (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y)
      (_hlimit : DiagonalTrace.IsDiagonalLimit ℓ Y hY D δ)
      (family : Family ℓ Y), Reference ℓ Y δ family → P) : P := by
  classical
  have hℓ : IsUnit (ℓ : k) := isUnit_iff_ne_zero.mpr
    (CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) Fact.out)
  have hY : IsUnit (ℓ : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using
      hℓ.map ((Y ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  obtain ⟨D, hcompletion, hsystem⟩ := exists_diagonalTowerSystem ℓ Y hY
  obtain ⟨δ, hlimit⟩ := completedLimit_exists ℓ Y hY D
    (diagonalTower_limit ℓ k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y hY D
      hcompletion hsystem)
  obtain ⟨family, ⟨reference⟩, _⟩ := diagonalTower_coefficients ℓ k (ringChar k)
    (Fact.out : ringChar k ≠ ℓ) Y hY D hcompletion hsystem δ hlimit
  exact finish hY D hcompletion hsystem δ hlimit family reference

private theorem triangleAdjunction
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [DiagonalTraceLocalizations ℓ Y]
    [DiagonalTraceLocalizations ℓ (ProjectiveLine Y)]
    [DiagonalTraceLocalizations ℓ (diagonalSurface Y)]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec ℓ (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec ℓ Y hY D)
    (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y)
    (hlimit : DiagonalTrace.IsDiagonalLimit ℓ Y hY D δ)
    (family : Family ℓ Y) (reference : Reference ℓ Y δ family) :
    Nonempty (push ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y ⊣
      exceptional ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y) := by
  exact
    ((rationalP1_triangle ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ)
      Y hY D hcompletion hsystem δ hlimit family reference).2.2.2.2.1).nonempty

/-- Supply the normalized strict cycle system, its unique completed limit, and its
coefficient realization to the projective-line triangle identities. -/
theorem rationalP1_adjunction_assembly
    (ℓ : ℕ) [Fact ℓ.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)] :
    Nonempty (push ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y ⊣
      exceptional ℓ c k (ringChar k) (Fact.out : ringChar k ≠ ℓ) Y) := by
  let := diagonalLocalizations ℓ Y
  let := diagonalLocalizations ℓ (ProjectiveLine Y)
  let := diagonalLocalizations ℓ (diagonalSurface Y)
  refine withCanonicalData ℓ k Y ?_
  intro hY D hcompletion hsystem δ hlimit family reference
  exact triangleAdjunction ℓ c k Y hY D hcompletion hsystem δ hlimit family reference

end AlgebraicGeometry.ProEtale.RationalP1
