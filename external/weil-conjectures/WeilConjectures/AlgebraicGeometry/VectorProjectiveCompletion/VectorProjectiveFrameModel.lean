/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveCompletionData
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis

set_option linter.privateModule false

/-! # Frame charts for a presented vector-bundle completion

Source: Stacks Project, Constructions, Tags 01OA, 01OE and 01NG.
(blueprint: lem-amb-vector-projective-frame-model). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pointwise
noncomputable section
namespace AlgebraicGeometry.VectorProjectiveCompletion
open VectorBundleZeroSection
private local instance restrictedSectionsModule (S : Scheme.{u}) (F : S.Modules) (V : S.Opens)
    (U : V.toScheme.Opens) : Module Γ(V.toScheme, U) Γ(F, V.ι ''ᵁ U) := by
  change Module Γ(S, V.ι ''ᵁ U) Γ(F, V.ι ''ᵁ U)
  infer_instance

end AlgebraicGeometry.VectorProjectiveCompletion
