/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 746, 16 November 2026 UTC:
Extract only the proof of M053.001 `DegreeData.frobeniusExponent_mul` from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, replace the source imports by the published
FrobeniusExponentMul.Statements module and the published proof module
ProfiniteInteger.U001.Proofs of M009.001 `proCIntegerOne_pow_nat_injective`,
add `open CyclicCohomology` for `extensionSubgroup`, drop the `@[simp]`
attribute and state the theorem as the published Statement applied to the
source parameters. Replace the citations of the
unpublished M014.014 `extensionNormalizedDegree_frobenius_eq_pow` by the
local private lemma `frobeniusExponent_mul_normalizedDegree_eq_pow`, whose
proof is the source proof of M014.014 (the second component of
`Exists.choose_spec σ.2`), and the rewrite by the unpublished M015.003
`frobeniusMul_coe` by the definitional `show`, matching its source proof
`rfl`. The calc chain is otherwise the original one. The original LICENSE
and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusExponentMul.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U001.Proofs

/-!
# The Frobenius exponent is additive

The exact proof that the exponent `n` with `deg σ = (1 : ℤ̂)^n` of a
Frobenius element is additive under the Frobenius semigroup multiplication.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Local copy of the source proof of M014.014: the normalized degree of a
Frobenius element is the chosen power of the positive generator. -/
private theorem frobeniusExponent_mul_normalizedDegree_eq_pow (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK σ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).2

/-- The exponent is additive under multiplication in the Frobenius
semigroup. -/
theorem frobeniusExponent_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    frobeniusExponent_mulStatement D K L hLK σ₁ σ₂ := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.extensionNormalizedDegree K L hLK (σ₁ * σ₂).1 :=
        (frobeniusExponent_mul_normalizedDegree_eq_pow D K L hLK
          (σ₁ * σ₂)).symm
    _ = D.extensionNormalizedDegree K L hLK σ₁.1 *
        D.extensionNormalizedDegree K L hLK σ₂.1 := by
      show D.extensionNormalizedDegree K L hLK (σ₁.1 * σ₂.1) = _
      rw [map_mul]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₁ *
        (Multiplicative.ofAdd (1 : ZHat)) ^
            D.frobeniusExponent K L hLK σ₂ := by
      rw [frobeniusExponent_mul_normalizedDegree_eq_pow,
        frobeniusExponent_mul_normalizedDegree_eq_pow]
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^
            (D.frobeniusExponent K L hLK σ₁ +
              D.frobeniusExponent K L hLK σ₂) := by
      rw [pow_add]

end DegreeData

end

end Langlands.NYLL.ClassFormation
