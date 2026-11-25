/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # The adjunction for locally constant integer-valued functions

Reuse the source module's private natural Hom equivalence through `import all`.
Source: Stacks Project, Tag 097D, and the cited source proof.
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The locally constant integer algebra functor is a right adjoint.

Source: Stacks Project, Tag 097D, and the private Hom equivalence in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
(auxiliary; not a blueprint node)

Proof: The existing Hom equivalence identifies maps from the connected components
of the prime spectrum of R to S with ring maps from locally constant integer
functions on S to R. Its inverse laws and naturality are already proved in the
source module. Applying adjunctionOfEquivLeft assembles the desired adjunction. -/
theorem profiniteToCommRingCatOp_isRightAdjoint :
    profiniteToCommRingCatOp.{u}.IsRightAdjoint :=
  ⟨_, ⟨Adjunction.adjunctionOfEquivLeft profiniteLocallyConstantHomEquiv
    profiniteLocallyConstantHomEquiv_naturality⟩⟩

end AlgebraicGeometry.ProEtale
