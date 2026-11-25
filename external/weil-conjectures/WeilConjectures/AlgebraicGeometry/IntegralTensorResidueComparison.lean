/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat

/-!
# Monoidal first-residue reduction

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md,
“The stratum”, displayed residue tensor isomorphism
(blueprint: lem-sfb-integral-tensor-residue-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Derived reduction of an ordinary tensor is the tensor of the two reductions
over the residue coefficient ring, rather than over the integral coefficient ring.

Source: det-lem-int-tensor-product.proof.md, “The stratum”, displayed formula.
(blueprint: lem-sfb-integral-tensor-residue-comparison).

Proof: compute the two derived objects on K-flat representatives P and Q. Ordinary
extension of scalars along the fixed quotient O_E -> O_E/pi_E is strong monoidal:
(P tensor Q) tensor O_E/pi_E identifies with
(P tensor O_E/pi_E) tensor_{O_E/pi_E} (Q tensor O_E/pi_E) by scalar associativity.
Extension sends K-flat representatives to K-flat representatives, and the direct-sum
total complexes have the same tensor associators. Localize this balanced comparison;
its inverse is the inverse balanced comparison. The derived comparison is independent
of the K-flat representatives by their quasi-isomorphism comparison. This is the
identity-geometric-map instance of the canonical derived tensor pullback comparison.
There is no constructibility, completeness or flatness hypothesis on M or N. -/
theorem integralTensorResidueComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) (M N : DerivedCategory (AdicCompletion.Modules l E S)) :
    Nonempty
      ((AdicCompletion.derivedReduction l E S 0).obj (M ⊗ N) ≅
        (AdicCompletion.derivedReduction l E S 0).obj M ⊗
          (AdicCompletion.derivedReduction l E S 0).obj N) := by
  let φ := AdicCompletion.quotient l E S 0
  let := Mod.extendScalarsMonoidal φ
  exact ⟨asIso (((Mod.extendScalars φ).leftDerivedTensorComparison.app M).app N)⟩

end AlgebraicGeometry.ProEtale
