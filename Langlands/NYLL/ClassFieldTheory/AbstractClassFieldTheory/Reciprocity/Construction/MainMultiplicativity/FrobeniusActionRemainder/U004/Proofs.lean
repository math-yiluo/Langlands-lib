/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5264, 15 November 2026:
Extract the proof of M053.004 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/FrobeniusActionRemainder.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import the published FrobeniusActionRemainder Statements
module and give the theorem the published proposition
frobeniusActionRemainder_mem_degreeKernelStatement as its type. The source
rewrites twice with extensionNormalizedDegree_frobenius_eq_pow (M014.014),
whose proof is not yet published; its one-line source proof
(Exists.choose_spec _.2).2 is used instead, as the local facts hσ and hφpow.
The rest of the proof is the source's. Omit open KummerTheory,
open CategoryTheory, the noncomputable section and all other source
declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainMultiplicativity.FrobeniusActionRemainder.Statements

/-!
# Frobenius action remainders have degree zero
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- If `φ` has Frobenius exponent one, its action remainder has normalized
degree zero. -/
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    frobeniusActionRemainder_mem_degreeKernelStatement D K L hLK φ σ hφ := by
  change D.extensionNormalizedDegree K L hLK
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1
  -- The source rewrites with M014.014 `extensionNormalizedDegree_frobenius_eq_pow`
  -- at `σ` and at `φ`; these are instances of its one-line source proof.
  have hσ : D.extensionNormalizedDegree K L hLK σ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK σ :=
    (Exists.choose_spec σ.2).2
  have hφpow : D.extensionNormalizedDegree K L hLK φ.1 =
      (Multiplicative.ofAdd (1 : ZHat)) ^ D.frobeniusExponent K L hLK φ :=
    (Exists.choose_spec φ.2).2
  rw [map_mul, map_pow, map_inv, hσ, hφpow, hφ, pow_one, mul_inv_cancel]

end DegreeData

end Langlands.NYLL.ClassFormation
