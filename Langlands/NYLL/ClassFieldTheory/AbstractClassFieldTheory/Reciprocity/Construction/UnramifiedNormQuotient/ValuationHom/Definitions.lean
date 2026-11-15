/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Normalized.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Extension.OfInclusion
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# The valuation homomorphism modulo an unramified degree

Modified by Worker 5264, 15 November 2026: extract the private definition
M058.007 `ValuationData.unramifiedValuationHom` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. The private source definition
is exposed as `Langlands.NYLL.PortInternal.M058.d007`, so the source
dot-notation call `v.unramifiedValuationHom K L hLK` reads
`PortInternal.M058.d007 v K L hLK`. Replace the source imports by focused
published imports, add a docstring, and omit the rest of the source file.
The universe-zero group variable, the `D` and `A` variables, the binders and
the body are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.PortInternal.M058

open ClassFormation
open KummerTheory
open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

/-- The normalized valuation on `A_K` followed by reduction modulo the degree
of the finite extension `L | K` (source: the private
`ValuationData.unramifiedValuationHom`). -/
def d007
    (v : ValuationData D A) (K : FiniteAbstractField G)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] :
    ambientFixedAddSubgroup A K.field →+
      ZMod ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ) :=
  (v.valueModulo
      ((FiniteAbstractFieldExtension.ofInclusion L K hLK).degree : ℕ)
      (FiniteAbstractFieldExtension.ofInclusion L K hLK).degree.property).comp
    (v.valuationAt K)

end

end Langlands.NYLL.PortInternal.M058
