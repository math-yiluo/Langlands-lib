/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
public import WeilConjectures.AlgebraicGeometry.CompletedConstantRealizationData
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.RingTheory.AdicCompletionNoetherian
public import WeilConjectures.RingTheory.FiniteModuleComplete
public import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullback
import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Completed adic coefficient datum and its strict reduction tower

Source: blueprint, proper base change, order 1239; Stacks Tags 099L and 099M
(blueprint: def-weil-pbc-adic-coefficient-datum).

The site has object universe t+1 and morphism universe t. Coefficients and modules
are in t+1. The ambient ring is the actual inverse limit of the finite constant
quotient sheaves, not the constant sheaf associated to the original ring.

## Main definitions

* `ProEtaleAdicCoefficientDatum`: coefficient hypotheses.
* `adicDatumRing`: the actual completed coefficient sheaf.
* `adicDatumAdjunction`: normalized derived scalar adjunction.
* `adicDatumDerivedTower`: universal strict quotient tower.
* `adicDatumModelTower`: its explicit K-flat computation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t r u v uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory

attribute [local irreducible] Functor.mapHomotopyCategory
  Functor.mapHomotopyCategoryFactors

namespace AlgebraicGeometry.Scheme

/-- The Noetherian, finitely generated, torsion, perfect and finite quotient hypotheses.
Source: blueprint order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
structure ProEtaleAdicCoefficientDatum (A : Type (t + 1)) [CommRing A]
    extends CompleteCoefficientDatum A where
  quotientFinite : ∀ n : ℕ, Finite (A ⧸ ideal ^ (n + 1))

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

section FiniteCoefficientComparison
variable (P : Type (t + 1)) [CommRing P] [Finite P]
variable [TopologicalSpace P] [DiscreteTopology P]

end FiniteCoefficientComparison

/-- The completed coefficient sheaf, with its genuine compatible-family sections.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumRing := adicLisseCompletedRing T d.ideal

/-- Module sheaves over the completed coefficient sheaf.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumModules := completedConstantModules T (adicDatumRing T d)

/-- Finite biproducts are the usual products in the abelian module category.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
instance adicDatumFiniteBiproducts : HasFiniteBiproducts (adicDatumModules T d) :=
  HasFiniteBiproducts.of_hasFiniteProducts

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original ring acts by its compatible residues in every finite quotient.
The projection equations determine this map uniquely.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the constant quotient maps form a cone, since the quotient maps compose.
Use the limit lift; its projection identities prove existence and uniqueness. -/
theorem adicDatumScalar_exists :
    ∃! φ : adicLisseConstantRing T A ⟶ adicDatumRing T d,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem T d.ideal) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1)))) := by
  let c : Cone (adicLisseRingSystem T d.ideal) :=
    { pt := adicLisseConstantRing T A
      π := NatTrans.ofOpSequence
        (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{t + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (d.ideal ^ (n + 1))))) (by
            intro n
            simp only [Functor.const_obj_map, adicLisseRingSystem,
              Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            congr 1) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro φ hφ
    apply limit.hom_ext
    intro n
    exact (hφ n.unop).trans (limit.lift_π c n).symm

/-- The unique compatible-residue coefficient map.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumScalar := (adicDatumScalar_exists T d).exists.choose

section ScalarChange

variable {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)

/-- Local pure tensors in the actual sheafified extension, transported by the
specified object identification of the additive scalar-extension witness.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum). -/
abbrev adicDatumTensorSection (M : completedConstantModules T R) (U : T.ProEtᵒᵖ)
    (s : S.obj.obj U) (m : M.val.obj U) :
    ((reductionChange T φ).obj M).val.obj U :=
  reductionTensorSection T φ M U s m

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem adicDatumOrdinaryAdjunction_formula :
    ∃ a : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ (M : completedConstantModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
        (a.unit.app M).val.app U x = adicDatumTensorSection T φ M U 1 x := by
  refine ⟨(ordinaryAdjunction_exists T φ).choose, ?_⟩
  intro M U x
  exact reductionUnit_apply T φ M U x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordinary tensor/restriction unit, fixed by its local pure-tensor formula.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the presheaf tensor unit m maps to 1 tensor m and then sheafifies.
Naturality on restrictions gives a sheaf map; tensor generation gives uniqueness. -/
theorem adicDatumOrdinaryUnit_exists (M : completedConstantModules T R) :
    ∃! u : M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M),
      ∀ (U : T.ProEtᵒᵖ) (m : M.val.obj U),
        u.val.app U m = adicDatumTensorSection T φ M U 1 m := by
  obtain ⟨a, ha⟩ := adicDatumOrdinaryAdjunction_formula T φ
  refine ⟨a.unit.app M, ha M, ?_⟩
  intro u hu
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (hu U x).trans (ha M U x).symm

/-- The ordinary unit, selected by the unique section formula.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryUnit (M : completedConstantModules T R) :
    M ⟶ (SheafOfModules.restrictScalars.{t + 1}
      ((adicLisseForget T).map φ)).obj ((reductionChange T φ).obj M) :=
  (adicDatumOrdinaryUnit_exists T φ M).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor/restriction adjunction normalized by the ordinary unit on every module.
Source: order 1239; Tag 03EK (blueprint: def-weil-pbc-adic-coefficient-datum).
Proof: the balanced map sends s tensor m to s times the proposed restricted map(m).
Sheafification extends it uniquely. Evaluation at 1 tensor m is its inverse;
the formulas commute with precomposition and postcomposition. -/
theorem adicDatumOrdinaryAdjunction_exists :
    ∃ adj : reductionChange T φ ⊣
        SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ),
      ∀ M : completedConstantModules T R, adj.unit.app M = adicDatumOrdinaryUnit T φ M := by
  obtain ⟨a, ha⟩ := adicDatumOrdinaryAdjunction_formula T φ
  refine ⟨a, ?_⟩
  intro M
  exact (adicDatumOrdinaryUnit_exists T φ M).unique (ha M)
    (adicDatumOrdinaryUnit_exists T φ M).exists.choose_spec

/-- The canonical ordinary scalar adjunction.
Source: order 1239 (blueprint: def-weil-pbc-adic-coefficient-datum). -/
def adicDatumOrdinaryAdjunction : reductionChange T φ ⊣
    SheafOfModules.restrictScalars.{t + 1} ((adicLisseForget T).map φ) :=
  (adicDatumOrdinaryAdjunction_exists T φ).choose

end ScalarChange

attribute [local irreducible] adicDatumRing adicLisseRingSystem

attribute [local instance 20000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

section Balancing
variable {R S B : Sheaf (ProEt.topology T) CommRingCat.{t + 1}}
variable (φ : R ⟶ S) (ψ : S ⟶ B)

section GenericKFlatTransport

open SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end GenericKFlatTransport

end Balancing

end AlgebraicGeometry.Scheme
