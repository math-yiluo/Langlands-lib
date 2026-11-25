/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealization.AdmissibleScalarRealizationExactSupplement

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData
public import Mathlib.Algebra.Homology.HomotopyCategory

/-! # Explicit ordinary reductions of the internal scalar model -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The complex whose localization defines the integral scalar model.
Source: blueprint, Compatible isomorphisms, constant finite-free scalar complex.
(blueprint: def-pe-internal-perfect-ordinary-reductions). -/
def internalPerfectIntegralComplex (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ) :
    CochainComplex (AdicCompletion.Modules l E W) ℤ :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI : (FiniteConstantModel.modelFunctor (Padic.coefficientExtensionIntegers l E) W).Additive :=
    by
      have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
        (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.2.2.2.2.2.2.2.2.1
      exact (AdmissibleScalarRealization.pid_scalar_assertions
        (Padic.coefficientExtensionIntegers l E) W).2.1
  let F := ModuleCat.uliftFunctor.{u + 1, u} (Padic.coefficientExtensionIntegers l E) ⋙
    FiniteConstantModel.modelFunctor (Padic.coefficientExtensionIntegers l E) W
  (F.mapHomologicalComplex (.up ℤ)).obj P

/-- Termwise ordinary extension along the actual integral-to-finite quotient.
Source: Stacks Tags 06YY and 09C6, ordinary reduction of a finite-free complex.
(blueprint: def-pe-internal-perfect-ordinary-reductions). -/
def internalPerfectOrdinaryReduction (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) :=
  ((Mod.extendScalars (AdicCompletion.quotient l E W n)).mapHomologicalComplex (.up ℤ)).obj
    (internalPerfectIntegralComplex l E W P)

/-- The ordinary balancing isomorphism for two consecutive reductions.
It is fixed by uniqueness of left adjoints and the actual quotient factorization.
Source: Stacks Tag 06YY, associativity of scalar extension.
(blueprint: def-pe-internal-perfect-ordinary-reductions). -/
def internalPerfectOrdinaryReductionStep (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) :
    ((Mod.extendScalars (AdicCompletion.transition l E W n)).mapHomologicalComplex (.up ℤ)).obj
        (internalPerfectOrdinaryReduction l E W P (n + 1)) ≅
      internalPerfectOrdinaryReduction l E W P n :=
  (Functor.mapHomologicalComplexCompIso
    ((Mod.extendScalarsComp (AdicCompletion.quotient l E W (n + 1))
      (AdicCompletion.transition l E W n)).symm ≪≫
      eqToIso (by congr 1; exact AdicCompletion.quotient_transition l E W n)) (.up ℤ)).app
    (internalPerfectIntegralComplex l E W P)

/-- Endomorphisms modulo chain homotopy of the ordinary quotient model.
Source: Stacks Tags 064B and 09C6.
(blueprint: def-pe-internal-perfect-ordinary-reductions). -/
abbrev internalPerfectOrdinaryHom (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) :=
  (HomotopyCategory.quotient _ (.up ℤ)).obj (internalPerfectOrdinaryReduction l E W P n) ⟶
    (HomotopyCategory.quotient _ (.up ℤ)).obj (internalPerfectOrdinaryReduction l E W P n)

/-- Ordinary scalar extension on homotopy classes, conjugated by balancing.
Source: Stacks Tag 09C6, reduction of chain maps and homotopies.
(blueprint: def-pe-internal-perfect-ordinary-reductions). -/
def internalPerfectOrdinaryHomStep (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) (f : internalPerfectOrdinaryHom l E W P (n + 1)) :
    internalPerfectOrdinaryHom l E W P n :=
  let H := HomotopyCategory.quotient _ (.up ℤ)
  let a := internalPerfectOrdinaryReductionStep l E W P n
  H.map a.inv ≫
    ((Mod.extendScalars (AdicCompletion.transition l E W n)).mapHomotopyCategory (.up ℤ)).map f ≫
      H.map a.hom

/-- The ordinary reduction step reduces a representative chain map and balances its scalars.
Source: functoriality of the homotopy quotient.
(blueprint: def-pe-internal-perfect-ordinary-reductions).
Proof: the induced homotopy functor sends a chain-map class to its scalar-extended class;
the quotient functor preserves the two compositions with the balancing isomorphism. -/
theorem internalPerfectOrdinaryHomStep_map (W : Scheme.{u})
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (n : ℕ) (f : internalPerfectOrdinaryReduction l E W P (n + 1) ⟶
      internalPerfectOrdinaryReduction l E W P (n + 1)) :
    internalPerfectOrdinaryHomStep l E W P n
        ((HomotopyCategory.quotient _ (.up ℤ)).map f) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((internalPerfectOrdinaryReductionStep l E W P n).inv ≫
          ((Mod.extendScalars (AdicCompletion.transition l E W n)).mapHomologicalComplex
            (.up ℤ)).map f ≫ (internalPerfectOrdinaryReductionStep l E W P n).hom) := by
  simp only [internalPerfectOrdinaryHomStep, Functor.mapHomotopyCategory_map,
    Functor.map_comp]

end AlgebraicGeometry.ProEtale
