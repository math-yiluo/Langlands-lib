/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Derived reduction towers over integral condensed coefficients

This module constructs the derived reduction tower in the first paragraph of
`definition-derived-adic-completeness--1` (blueprint: def-weil-integral-reduction-tower).
Source: `literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-localization-completion/sk-def-pe-derived-completion/def-pe-derived-complete.md`,
first paragraph.
The quotient coefficient maps are the canonical quotient maps on continuous
integer-valued functions, pulled back along the pro-etale point map.  The
compatibility theorem follows from the quotient identity by functoriality.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The quotient of the integral coefficient ring by the `n`th power of a
chosen uniformizer ideal.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-localization-completion/sk-def-pe-derived-completion/def-pe-derived-complete.md,
first paragraph (blueprint: def-weil-integral-reduction-tower).
-/
noncomputable abbrev integralQuotient (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)]
    (π : PadicAlgCl.integers ell E) (n : ℕ) : Type :=
  PadicAlgCl.integers ell E ⧸ (Ideal.span ({π} : Set (PadicAlgCl.integers ell E))) ^ n

/-- The condensed ring of continuous functions into the finite quotient.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-localization-completion/sk-def-pe-derived-completion/def-pe-derived-complete.md,
first paragraph (blueprint: def-weil-integral-reduction-tower).
-/
noncomputable abbrev integralQuotientRingObj (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)]
    (π : PadicAlgCl.integers ell E) (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E
  Profinite.continuousMapRingObj (integralQuotient ell E π n)

/-- The quotient map on condensed rings.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-localization-completion/sk-def-pe-derived-completion/def-pe-derived-complete.md,
first paragraph (blueprint: def-weil-integral-reduction-tower).
-/
noncomputable def integralReductionRingMap (ell : ℕ) [Fact ell.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ell)]
    (π : PadicAlgCl.integers ell E) (n : ℕ) :
    Profinite.padicIntegersRingObj.{u} ell E ⟶ integralQuotientRingObj ell E π n :=
  letI := PadicAlgCl.normedFieldOfAlgebra ell E
  (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (Profinite.continuousMapRingSheafMap (Ideal.Quotient.mk _) continuous_quot_mk)

/-- The pulled-back integral coefficient map.
Source: literature/blueprint/latest/blueprint/part-six-operations/sec-proetale-coefficients/
sec-pe-localization-completion/sk-def-pe-derived-completion/def-pe-derived-complete.md,
first paragraph (blueprint: def-weil-integral-reduction-tower).
-/
noncomputable abbrev integralReductionCoefficientMap (X : Scheme.{u})
    (ell : ℕ) [Fact ell.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ell)]
    (π : PadicAlgCl.integers ell E) (n : ℕ) :
    condensedRingObj (Profinite.padicIntegersRingObj ell E) X ⟶
      condensedRingObj (integralQuotientRingObj ell E π n) X :=
  coefficientMap (integralReductionRingMap ell E π n) X

end AlgebraicGeometry.ProEtale
