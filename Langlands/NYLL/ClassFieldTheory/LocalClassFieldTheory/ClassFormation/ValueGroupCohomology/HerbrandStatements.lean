/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 230, 14 November 2026: extract the statement types of
M141.004, M141.006, M141.009 and M141.010 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix namespaces with
Langlands.NYLL; import the published action, reduction homomorphism and
Herbrand quotient data; replace theorem declarations by Prop-valued
definitions with the Statement suffix. The source universe, variable
telescope, explicit sigma binder and local action bindings are preserved.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ValueGroupCohomology.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

universe u

open Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

def galoisGroupValueGroupFixedToZModHom_kerStatement : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    MonoidHom.ker (galoisGroupValueGroupFixedToZModHom K L) =
      (tateNormSubgroup (Gal(L / K)) (Multiplicative Int)).subgroupOf
        (fixedSubgroup (Gal(L / K)) (Multiplicative Int))

def galoisGroupValueGroupHerbrandH0FiniteStatement : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite (HerbrandH0 (Gal(L / K)) (Multiplicative Int))

def galoisGroupValueGroup_normKernelSubgroup_eq_botStatement : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    normKernelSubgroup (Gal(L / K)) (Multiplicative Int) = ⊥

def galoisGroupValueGroupHerbrandHMinusOneFiniteStatement
    (σ : Gal(L/K)) : Prop :=
    letI := galoisGroupValueGroupMulDistribMulAction K L
    Finite
      (HerbrandHMinusOne (Gal(L / K)) (Multiplicative Int) σ)

end
end Langlands.NYLL.LocalClassFieldTheory
