/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions

/-!
# Norm images in degree-zero Tate cohomology of units: targets

Modified by Worker 5454: extract the asserted types of M095.002
`CyclicCohomology.unitsNorm_mem_invariants` (lines 36–39), M095.007
`CyclicCohomology.additive_toMul_finset_sum_units` (lines 105–110) and M095.009
`CyclicCohomology.additiveNormSubgroup_eq_ker_quotient_map` (lines 123–127)
from the pinned NYLL `Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean` as
Prop-valued definitions. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to each lemma name, keep every source parameter in order and
binder kind, and omit the proofs and the `@[simp]` attribute of M095.007.
The imports are the sibling data module of this port and the published
M093.005 module (`normClass`). The source's `open CategoryTheory` is omitted
because no target uses it. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

/-- The additive unit norm is fixed by the Galois action. -/
def unitsNorm_mem_invariantsStatement (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] (x : Additive Lˣ) : Prop :=
  unitsNormLinearMap K L x ∈ unitsInvariantSubmodule K L

/-- A finite sum of additive units corresponds to the product of their underlying units. -/
def additive_toMul_finset_sum_unitsStatement {ι : Type*} (L : Type*) [Field L]
    (s : Finset ι) (f : ι → Additive Lˣ) : Prop :=
  Additive.toMul (Finset.sum s f) =
    Finset.prod s (fun i => Additive.toMul (f i))

/-- The additive norm subgroup is the kernel of the norm-quotient map. -/
def additiveNormSubgroup_eq_ker_quotient_mapStatement (K L : Type u)
    [Field K] [Field L] [Algebra K L] : Prop :=
  additiveNormSubgroup K L =
    (MonoidHom.toAdditive (normClass K L)).ker

end

end Langlands.NYLL.CyclicCohomology
