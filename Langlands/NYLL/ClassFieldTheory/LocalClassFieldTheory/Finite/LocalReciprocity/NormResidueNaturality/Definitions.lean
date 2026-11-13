/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: moved LocalClassFieldTheory.intermediateFieldRestrictContinuous
to Langlands.NYLL.LocalClassFieldTheory.intermediateFieldRestrictContinuous and split
out this single definition (inventory M261.001). The source's
RamificationTheory.intermediateFieldRestrictNormalHom is the published
Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom. The NYLL
imports are replaced by that definition module and four Mathlib modules, and the
source's open LocalFieldTheory and open RamificationTheory become
open Langlands.NYLL.RamificationTheory. The section variables, telescope, return
type and body are unchanged.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction.Definitions
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous restriction between finite Galois intermediate fields

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean`,
lines 19–38 (inventory M261.001).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.RamificationTheory

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Restriction between the actual Galois groups of two finite intermediate
fields, bundled as a continuous homomorphism for their finite Krull
topologies. -/
noncomputable def intermediateFieldRestrictContinuous
    (E F : IntermediateField K (SeparableClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsGalois K E] [IsGalois K F] :
    Gal(F / K) →ₜ* Gal(E / K) :=
  { intermediateFieldRestrictNormalHom E F hEF with
    continuous_toFun := continuous_of_discreteTopology }

end Langlands.NYLL.LocalClassFieldTheory
