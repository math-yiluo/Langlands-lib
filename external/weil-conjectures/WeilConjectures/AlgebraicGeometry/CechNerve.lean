/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.AlgebraicTopology.CechNerve

/-!
# The terms of the Čech nerve of a nonempty scheme are nonempty

Blueprint `rem-sf-cech-truncation-obstruction` (i): for a morphism of schemes `f : W ⟶ U` with
`W` nonempty (for instance a weakly contractible pro-étale covering `W → U` of a nonempty
object), every term `W ×_U ⋯ ×_U W` of the Čech nerve of `f` is nonempty, since it contains the
diagonal copy of `W`. So no truncation of the Čech hypercover of `f` is a hypercovering, and a
bound on the length of this hypercovering is not available.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `rem-sf-cech-truncation-obstruction` (i): every term of the Čech nerve of a
morphism of schemes `f : W ⟶ U` with nonempty source is nonempty: it receives the diagonal from
`W` (`CategoryTheory.Arrow.cechNerveDiagonal`). -/
theorem Scheme.nonempty_cechNerve_obj {W U : Scheme} (f : W ⟶ U) [Nonempty W]
    (n : SimplexCategoryᵒᵖ) : Nonempty ((Arrow.mk f).cechNerve.obj n) :=
  ⟨((Arrow.mk f).cechNerveDiagonal n).base (Classical.arbitrary W)⟩

end AlgebraicGeometry
