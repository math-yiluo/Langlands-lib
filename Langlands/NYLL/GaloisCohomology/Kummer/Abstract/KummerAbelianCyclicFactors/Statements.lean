/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions
import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianCyclicFactors.Definitions

/-!
# NYLL M020: cyclic factor targets

Modified by Worker 4918: state the source theorems M020.001
`finiteCommGroup_exists_jointlyFaithful_cyclic_factors`, M020.008
`extensionSubgroup_isClosed` and M020.009 `cyclicFactorSubgroup_isClosed` of
the pinned NYLL
`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianCyclicFactors.lean` as
Prop-valued definitions ending in `Statement`, with the source binders and
statements, under the namespace prefix `Langlands.NYLL`. Proofs are omitted.
The source's module import is replaced by its Mathlib import and the ports of
the two NYLL declarations the statements use. The paired Markdown records
every modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

open CyclicCohomology

noncomputable section

section FiniteAbelianCyclicFactors

/-- Target M020.001: coordinate characters obtained from the structure theorem
separate the elements of a finite commutative group. -/
def finiteCommGroup_exists_jointlyFaithful_cyclic_factorsStatement
    (Q : Type*) [CommGroup Q] [Finite Q] : Prop :=
  ∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
    (∀ i, 1 < m i) ∧
    ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
      (∀ i, Function.Surjective (f i)) ∧
      (⨅ i, MonoidHom.ker (f i)) = ⊥

end FiniteAbelianCyclicFactors

section ClosedCyclicSubextensions

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Target M020.008: a closed abstract field subgroup `G_L` remains closed when
regarded as a subgroup of the larger abstract field subgroup `G_K`. -/
def extensionSubgroup_isClosedStatement
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup) : Prop :=
  IsClosed (extensionSubgroup (G := G) K L hLK : Set K.toSubgroup)

-- The source's `variable [IsTopologicalGroup G]` (line 144) belongs to the
-- telescope of the source theorem below. A `def` would not include this
-- unused section instance, so it is bound explicitly as the first binder.

set_option linter.unusedVariables false in
/-- Target M020.009: a pulled-back cyclic factor kernel is closed inside `G_K`:
the finite quotient by `G_L` is discrete, and the factor kernel is pulled back
along the continuous quotient map. -/
def cyclicFactorSubgroup_isClosedStatement [IsTopologicalGroup G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hnormal : (extensionSubgroup (G := G) K L hLK).Normal]
    [hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK)]
    {C : Type*} [Group C]
    (f : (K.toSubgroup ⧸ extensionSubgroup (G := G) K L hLK) →* C) : Prop :=
  IsClosed
    (cyclicFactorSubgroup (extensionSubgroup (G := G) K L hLK) f :
      Set K.toSubgroup)

end ClosedCyclicSubextensions

end

end Langlands.NYLL.KummerTheory
