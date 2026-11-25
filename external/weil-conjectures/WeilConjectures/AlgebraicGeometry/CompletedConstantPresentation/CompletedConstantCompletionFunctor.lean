/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantProjectionMaps
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
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

/-! # Functoriality of completed constant modules

Source: Stacks Project, Modules on Sites, Tags 093J--093M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 1024
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
namespace CompletedConstantPresentation

variable (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)

/-- The quotient tower, with the maps induced by completion-linear maps.
Source: Stacks Tags 093J--093M
(blueprint: def-weil-pbc-completed-constant-completion-functor). -/
def tower : ModuleCat.{u + 1} (AdicCompletion I A) ⥤
    (ℕᵒᵖ ⥤ SheafOfModules.{u + 1} (adicLisseRing X A)) where
  obj N := adicLisseModuleSystem X I (completedConstantUnderlyingModule I N)
  map f := NatTrans.ofOpSequence (fun n ↦ (adicLisseConstantModules X A).map
    (completedConstantQuotientMap I
      ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map f) n)) (by
        intro n
        simp only [adicLisseModuleSystem, Functor.ofOpSequence_map_homOfLE_succ,
          ← Functor.map_comp]
        congr 1
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using Submodule.Quotient.induction_on with
        | _ x => rfl)
  map_id N := by
    apply NatTrans.ext
    funext n
    change (adicLisseConstantModules X A).map _ = 𝟙 _
    rw [← (adicLisseConstantModules X A).map_id]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    change (adicLisseConstantModules X A).map _ =
      (adicLisseConstantModules X A).map _ ≫ (adicLisseConstantModules X A).map _
    rw [← Functor.map_comp]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- The actual inverse-limit functor on constant quotient modules.
Source: Stacks Tags 093J--093M
(blueprint: def-weil-pbc-completed-constant-completion-functor). -/
def completion : ModuleCat.{u + 1} (AdicCompletion I A) ⥤
    SheafOfModules.{u + 1} (adicLisseRing X A) := tower X I ⋙ lim

instance tower_additive : (tower X I).Additive := by
  have := CompletedConstantReduction.constant_additive X A
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  change (adicLisseConstantModules X A).map _ =
    (adicLisseConstantModules X A).map _ + (adicLisseConstantModules X A).map _
  rw [← Functor.map_add]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => rfl

instance completion_additive : (completion X I).Additive := by
  constructor
  intro M N f g
  apply limit.hom_ext
  intro n
  change limMap ((tower X I).map (f + g)) ≫ limit.π _ n =
    (limMap ((tower X I).map f) + limMap ((tower X I).map g)) ≫ limit.π _ n
  rw [Functor.map_add, Preadditive.add_comp, limMap_π, limMap_π, limMap_π]
  simp only [NatTrans.app_add, Preadditive.comp_add]

/-- Tensor realization, retaining the constant A-action.
Source: Stacks Tag 093M
(blueprint: def-weil-pbc-completed-constant-completion-functor). -/
def realization
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :=
  completedConstantRealization X I φ ⋙
    SheafOfModules.restrictScalars ((adicLisseForget X).map (completedConstantBaseMap X I φ))

instance realization_additive
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :
    (realization X I φ).Additive := by
  have := CompletedConstantReduction.constant_additive X (AdicCompletion I A)
  unfold realization completedConstantRealization
  infer_instance

/-- Tensor realization is right exact on all modules.
Source: Stacks Tags 03D7, 03DA and 093J
(blueprint: def-weil-pbc-completed-constant-completion-functor).
Proof: constant sheafification preserves finite colimits, scalar extension is left
adjoint to restriction, and restriction preserves finite colimits. -/
theorem realization_preservesFiniteColimits
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I) :
    PreservesFiniteColimits (realization X I φ) := by
  have := (CompletedConstantReduction.constant_exact X (AdicCompletion I A)).2
  obtain ⟨_, hr, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨a, _⟩ := ha (completedAdicChange X φ)
    (completedAdicChangeData X φ).choose_spec.choose
    (fun f ↦ (completedAdicChangeData X φ).choose_spec.choose_spec.choose f)
  have := a.isLeftAdjoint
  have : PreservesFiniteColimits (completedAdicChange X φ) := inferInstance
  have := (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (completedConstantBaseMap X I φ)).choose_spec.choose
  unfold realization completedConstantRealization
  change PreservesFiniteColimits
    ((adicLisseConstantModules X (AdicCompletion I A) ⋙ completedAdicChange X φ) ⋙ _)
  infer_instance

variable [IsNoetherianRing A]

/-- The fixed comparison maps form a natural transformation.
Source: Stacks Tags 093J--093M and the proved finite projection naturality
(blueprint: def-weil-pbc-completed-constant-completion-functor).
Proof: test naturality after every limit projection; it is precisely the already
proved naturality of the finite residue projections. -/
def comparison
    (φ : adicLisseConstantRing X (AdicCompletion I A) ⟶ adicLisseCompletedRing X I)
    (hφ : ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem X I) (op n) =
      (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (AdicCompletion.evalₐ I (n + 1)).toRingHom)) :
    realization X I φ ⟶ completion X I where
  app N := completedConstantComparisonMap X I φ hφ N
  naturality {M N} f := by
    apply limit.hom_ext
    intro n
    induction n using Opposite.rec with
    | _ n =>
      change (realization X I φ).map f ≫ completedConstantComparisonMap X I φ hφ N ≫
        limit.π _ (op n) =
          completedConstantComparisonMap X I φ hφ M ≫ limMap _ ≫ limit.π _ (op n)
      rw [limMap_π, completedConstantComparisonMap_π,
        ← Category.assoc, completedConstantComparisonMap_π]
      exact completedConstantProjection_naturality X I φ hφ f n

end CompletedConstantPresentation
end AlgebraicGeometry.Scheme
