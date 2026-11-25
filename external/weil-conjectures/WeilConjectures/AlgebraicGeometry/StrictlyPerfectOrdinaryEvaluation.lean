/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly

/-! # Ordinary evaluation for a strictly perfect complex

Source: Stacks Project, Cohomology of Sheaves, Tags 08DQ and 08DM.
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation).
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Ordinary evaluation is degreewise invertible for a strictly perfect first input.
There is no bound on the second complex and the open need not be affine.
Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, proof of Lemma 20.50.5,
and Tag 08DM, proof of Lemma 20.46.9.
(blueprint: lem-pc-strictly-perfect-ordinary-evaluation).

Proof: in degree q, the dual Hom complex has just the possibly nonzero factor
Hom(P^(-q),O); all other target terms of O[0] are zero. The bounded support of P
makes the tensor summands in any total degree finite. The Hom complex on the
right likewise has finitely many possibly nonzero factors. Under these product
and coproduct identifications, the specified formula is the sum of the maps
F^p tensor Hom(P^(-q),O) to Hom(P^(-q),F^p), with p+q=n. For a finite free
module this is the identity on finitely many copies of F^p, by evaluation on
basis sections. A retraction of P^(-q) from a finite free module gives a
retraction of this comparison; naturality restricts the inverse to that
retraction. Thus each block, and hence every degree map, is invertible.
The argument also covers rank zero, P=0, empty U, and unbounded F. -/
theorem isIso_localOrdinaryEvaluation_degree (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) (n : ℤ) : IsIso (f.f n) := by
  apply boundedOrdinaryEvaluation_degree X U P F hstrict.1 ?_ n f hf
  intro r B
  exact SheafOfModules.isIso_moduleDualEvaluation_of_retract
    (X.sheaf.over U) (P.X r) B (hstrict.2 r)

end AlgebraicGeometry
