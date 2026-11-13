/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the M266.012/.018/.019 theorem
statements from commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL and close each original telescope
under universal quantifiers in a Prop-valued definition with a Statement
suffix. Import only the published data needed for these targets.
Source proofs and simp attributes are reserved for proof contributions.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U011.Definitions
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U006.Definitions

/-!
# The unramified norm subgroup: proposition targets

Source: M266.012/.018/.019 in
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Membership is divisibility of the normalized unit valuation by n. -/
def mem_unramifiedNormSubgroup_iffStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ),
    x ∈ unramifiedNormSubgroup K n ↔
      (n : Int) ∣ LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x)

/-- The kernel of the multiplicative reduced valuation equals the published unramified norm subgroup. -/
def unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHomStatement : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat),
    MonoidHom.ker (valuationModDegreeMulHom K n) = unramifiedNormSubgroup K n

/-- Membership is equivalent to the multiplicative reduced valuation being one. -/
def mem_unramifiedNormSubgroup_iff_valuationModDegreeMulHom_eq_oneStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : Nat) (x : Kˣ),
    x ∈ unramifiedNormSubgroup K n ↔ valuationModDegreeMulHom K n x = 1

end Langlands.NYLL.LocalClassFieldTheory
