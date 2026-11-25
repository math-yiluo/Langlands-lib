/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteStageRationalExchange.FiniteStageRationalExchangeData
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemKaroubi

/-! # Supported extension on the actual coefficient systems

Source: sketch32, lines 1208--1228 and 1291--1321.
(blueprint: lem-sbc-finite-stage-karoubi-extension)
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
variable {U V : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim V ≤ n)]
  [Fact (∀ x : U, IsUnit (l : U.presheaf.stalk x))]
  [Fact (∀ x : V, IsUnit (l : V.presheaf.stalk x))]
end AlgebraicGeometry.Scheme.FiniteStageRationalExchange
