/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedTowerRoos
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedProjectionAdjunction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCompletedObjectReconstruction
import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerFiniteReduction

/-! # Canonical reconstruction adjunction for completed ell-power towers

Source: latest blueprint, chap-Smooth-purity, sk-lem-sp-tower-equivalence.proof.md;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: lem-sp-completed-reduction-adjunction).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

end AlgebraicGeometry.ProEtale
