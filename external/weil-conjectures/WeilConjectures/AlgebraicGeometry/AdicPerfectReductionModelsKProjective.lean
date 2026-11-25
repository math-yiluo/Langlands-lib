/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes
import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientTermsProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # K-projectivity of ordinary quotient complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction
  adicPerfectLocalComplex derivedExtension extend change
  adicPerfectQuotientComplex adicPerfectQuotientStep

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- K-projectivity of the ordinary quotient complexes.
Source: Stacks Project, Tags 06YY, 064B and 09C5.
(auxiliary; not a blueprint node).

Proof: every finite projective term of P is a retract of a finite free module.
Constant realization, scalar extension and slice restriction preserve these retract
maps and their identity composite. Each quotient term is consequently a retract
of a finite sum of copies of the unit sheaf. On the weakly contractible slice,
Hom from the unit is evaluation at the final object, which preserves epimorphisms.
Thus the unit is projective, as are its finite sums and retracts. Termwise additive
functors preserve the upper bound b. Apply the bounded-above projective-complex
criterion to obtain K-projectivity. The argument includes zero terms, zero rings,
the unit ideal and empty slices, since retracts and exact evaluation still apply. -/
theorem adicPerfectReductionModels_kprojective (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let R := fun n : ℕ ↦
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U
    let C : (n : ℕ) → Cx (R n) := fun n ↦ adicPerfectQuotientComplex.{u, v} X J U P n
    ∀ n : ℕ, (C n).IsKProjective := by
  dsimp only
  intro n
  let := _hb
  have : ∀ i : ℤ, Projective
      ((adicPerfectQuotientComplex.{u, v} X J U P n).X i) :=
    adicPerfectQuotientComplex_terms_projective.{u, v} X J U _hU P _hP n
  have : (adicPerfectQuotientComplex.{u, v} X J U P n).IsStrictlyLE b := by
    unfold adicPerfectQuotientComplex adicPerfectLocalComplex
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ b

end AlgebraicGeometry.Scheme
