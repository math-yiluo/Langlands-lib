/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.FiniteStageRationalExchangeData

import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.RationalRawOperationCoherence
import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.FiniteStageKaroubiExtension

/-! # Coefficient coherence for one completed operation pair

Source: sketch32, lines 1218--1228 and 1291--1321.
(blueprint: lem-sbc-rational-operation-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Idempotents AlgebraicGeometry WeilConjectures
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteStageRationalExchange

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section Operations

variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [dU : Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [dV : Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [iU : Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [iV : Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
  (q : U ⟶ V)

end Operations
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
