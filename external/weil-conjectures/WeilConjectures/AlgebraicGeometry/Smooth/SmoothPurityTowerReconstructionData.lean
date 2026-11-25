/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.EllCoefficientFiber
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset

import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian

/-!
# Completed evaluations and the canonical tower reconstruction map

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-lem-sp-tower/_section.md`; Stacks Project, Tags 0940 and 099P
(blueprint: def-sp-tower-reconstruction-data).

The natural index n denotes positive exponent n+1. A Roos triangle specifies the
actual derived inverse limit and its projections. The comparison at each finite level
is the tensor-restriction adjoint of that projection, in the finite-coefficient category.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The small pro-etale site fits in the actual coefficient universe.
Source: blueprint, coefficient setup (blueprint: def-sp-tower-reconstruction-data). -/
instance (priority := 4000) spReconstructionSiteSmall : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The fixed-universe abelian structure used by the reconstruction interface.
This specializes the ordinary module-sheaf structure without leaving the coefficient
universe undetermined. Source: Stacks, Modules on Sites
(blueprint: def-sp-tower-reconstruction-data). -/
instance (priority := 3000) spReconstructionModulesAbelian
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1}) :
    Abelian (SheafOfModules.{u + 1} R) := SheafOfModules.instAbelian R

/-- The same projection retaining the existing commutative ring structures.
Source: blueprint, coefficient setup (blueprint: def-sp-tower-reconstruction-data). -/
def spCompletedEllCommProjection (n : ℕ) :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      (spCoefficientCommRings l E T).obj (op n) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
      (spCompletedEllProjection.{u, u} l E T n)

/-- Exact restriction from the actual ell-power quotient to completed coefficients.
Source: blueprint, restriction in proof step 2 (blueprint: def-sp-tower-reconstruction-data). -/
abbrev spCompletedEllRestriction (n : ℕ) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (spCompletedEllCommProjection l E T n))

variable (D : SpCoefficientTowersAbelian l E T)

/-- The given tower's level as a module over the completed ring, without changing its
underlying sheaf or transition. Source: blueprint, proof step 2
(blueprint: def-sp-tower-reconstruction-data). -/
def spCompletedEvaluation (n : ℕ) : spCoefficientTowers l E T ⥤
    WeilConjectures.scalarReductionSource.{u, u} l E T :=
  spCoefficientEvaluation l E T D.equivalence n ⋙ spCompletedEllRestriction l E T n

private theorem spCompletedEllProjection_comp {m n : ℕ} (h : m ≤ n) :
    spCompletedEllProjection.{u, u} l E T n ≫
      (spCoefficientRings l E T).map (homOfLE h).op =
        spCompletedEllProjection.{u, u} l E T m := by
  unfold spCompletedEllProjection
  rw [Category.assoc, limit.w]

private theorem spCompletedEllCommProjection_comp {m n : ℕ} (h : m ≤ n) :
    spCompletedEllCommProjection l E T n ≫
      (spCoefficientCommRings l E T).map (homOfLE h).op =
        spCompletedEllCommProjection l E T m := by
  let F := sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  rw [F.map_comp]
  simp only [spCompletedEllCommProjection]
  dsimp only [F]
  rw [Functor.map_preimage, Functor.map_preimage]
  have hm : F.map ((spCoefficientCommRings l E T).map (homOfLE h).op) =
      (spCoefficientRings l E T).map (homOfLE h).op := by
    exact eq_of_heq (Functor.hcongr_hom (coefficientRings_eq l E T) (homOfLE h).op).symm
  rw [hm]
  exact spCompletedEllProjection_comp l E T h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The unique ordinary transition, fixed on every section by the original strict
semilinear tower. Source: blueprint, proof step 2 (blueprint: def-sp-tower-reconstruction-data).
Proof: the completed projections commute with quotient transitions by the limit-cone
condition. Thus the original semilinear transition becomes completed-ring linear.
It commutes with sheaf restrictions and tower morphisms. Equality on all sections
determines each component uniquely. -/
theorem spCompletedTransition_existsUnique (n : ℕ) :
    ∃! τ : spCompletedEvaluation l E T D (n + 1) ⟶ spCompletedEvaluation l E T D n,
      ∀ (M : spCoefficientTowers l E T) (U : T.ProEtᵒᵖ)
        (x : ((spCompletedEvaluation l E T D (n + 1)).obj M).val.obj U),
        (τ.app M).val.app U x =
          (((D.equivalence.functor.obj M).transition (Nat.le_succ n)).val.app U) x := by
  let τ : spCompletedEvaluation l E T D (n + 1) ⟶ spCompletedEvaluation l E T D n :=
    { app M :=
        { val :=
            { app U := ModuleCat.ofHom
                (X := ((spCompletedEvaluation l E T D (n + 1)).obj M).val.obj U)
                (Y := ((spCompletedEvaluation l E T D n).obj M).val.obj U)
                { toFun := fun x ↦
                    ((D.equivalence.functor.obj M).transition (Nat.le_succ n)).val.app U x
                  map_add' := map_add _
                  map_smul' := by
                    intro r x
                    have he := congrArg (fun f ↦ f.hom.app U r)
                      (spCompletedEllCommProjection_comp l E T (Nat.le_succ n))
                    change ((spCoefficientCommRings l E T).map
                      (homOfLE (Nat.le_succ n)).op).hom.app U
                        ((spCompletedEllCommProjection l E T (n + 1)).hom.app U r) =
                          (spCompletedEllCommProjection l E T n).hom.app U r at he
                    have hh := (((D.equivalence.functor.obj M).transition
                      (Nat.le_succ n)).val.app U).hom.map_smul
                        ((spCompletedEllCommProjection l E T (n + 1)).hom.app U r)
                        (show ((D.equivalence.functor.obj M).level (n + 1)).val.obj U
                          from x)
                    exact hh.trans (congrArg
                      (fun a : ((spCoefficientCommRings l E T).obj (op n)).obj.obj U ↦
                        a • (show ((D.equivalence.functor.obj M).level n).val.obj U
                          from ((D.equivalence.functor.obj M).transition
                            (Nat.le_succ n)).val.app U x)) he)
                }
              naturality := by
                intro U V f
                ext x
                exact PresheafOfModules.naturality_apply
                  ((D.equivalence.functor.obj M).transition (Nat.le_succ n)).val f x } }
      naturality := by
        intro M N f
        ext U x
        have h := congrArg (fun a ↦ a.val.app U x)
          ((D.equivalence.functor.map f).comm (Nat.le_succ n))
        change (((D.equivalence.functor.obj N).transition (Nat.le_succ n)).val.app U)
            (((D.equivalence.functor.map f).app (n + 1)).val.app U x) =
          ((D.equivalence.functor.map f).app n).val.app U
            (((D.equivalence.functor.obj M).transition (Nat.le_succ n)).val.app U x)
        exact h }
  refine ⟨τ, ?_, ?_⟩
  · intro M U x
    rfl
  · intro σ hσ
    ext M U x
    exact hσ M U x

/-- The original transition with its restricted scalar action, selected only from
its sectionwise unique characterization. Source: blueprint, proof step 2
(blueprint: def-sp-tower-reconstruction-data). -/
def spCompletedTransition (n : ℕ) :
    spCompletedEvaluation l E T D (n + 1) ⟶ spCompletedEvaluation l E T D n :=
  (spCompletedTransition_existsUnique l E T D n).exists.choose

/-- Derived level evaluation followed by exact completed-coefficient restriction.
Source: blueprint, proof step 2 (blueprint: def-sp-tower-reconstruction-data). -/
def spDerivedCompletedEvaluation (n : ℕ) : spDerivedCoefficientTowers l E T D ⥤
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  spDerivedCoefficientEvaluation l E T D n ⋙
    (spCompletedEllRestriction l E T n).mapDerivedCategory

end AlgebraicGeometry.ProEtale
