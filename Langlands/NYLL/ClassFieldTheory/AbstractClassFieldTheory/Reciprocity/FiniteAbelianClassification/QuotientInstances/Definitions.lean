/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions

/-!
# NYLL M298.001–.002: local quotient instances of a finite abelian subextension

Modified by Worker 458, 14 November 2026: extract the two source local
instances M298.001 and M298.002 (lines 36–46) of the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`. Prefix the namespace with
`Langlands.NYLL`, rename the two instances to the reserved fresh names
`Langlands.NYLL.PortInternal.M298.d001` and `Langlands.NYLL.PortInternal.M298.d002`,
replace the source imports by the single published import these declarations
use, drop the unused section variables and `open KummerTheory`, and add a
docstring to each instance. Binders, binder kinds, the `local` instance scope
and the bodies are otherwise unchanged. The paired Markdown records every
modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

As in the source, both instances are `local`: their instance attribute ends
with the enclosing namespace below and is not exported. A consumer that needs
the source scope installs them with
`attribute [local instance] Langlands.NYLL.PortInternal.M298.d001
Langlands.NYLL.PortInternal.M298.d002`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

namespace FiniteAbelianSubextension

/-- Source local instance `extensionQuotient_normal`: the subgroup representing
a finite abelian subextension is normal in the base subgroup. -/
local instance _root_.Langlands.NYLL.PortInternal.M298.d001
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- Source local instance `representedQuotient_finite`: the raw quotient
represented by a finite abelian subextension is finite. -/
local instance _root_.Langlands.NYLL.PortInternal.M298.d002
    {G : Type*} [Group G] [TopologicalSpace G] {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  L.finite

end FiniteAbelianSubextension

end Langlands.NYLL.ClassFormation
