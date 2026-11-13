/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 121, 2026-11-13: extract the types of the theorem
M239.004 `residueAction_ker` (line 54) and of the Prop-valued instances
M239.005 `inertiaGroup_normal` (line 59) and M239.038
`decompositionField_isGalois` (line 371) of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ValuationSubring.lean`
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the
namespace with Langlands.NYLL and package each complete elaborated source
telescope (section variables first, then the declaration's own binders) as a
closed Prop-valued definition named with the suffix `Statement`. The two
instance targets are `abbrev`s, so that a proof can be registered as an
instance. Proofs and the instance attributes are omitted; the imports are the
published M239 data module.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring.Definitions

/-!
# Hilbert ramification theory: valuation-subring statement targets

Closed statement targets for NYLL M239.004 (the inertia group is the kernel of
the residue action), M239.005 (the inertia group is normal in the decomposition
group) and M239.038 (for finite-dimensional `L / K`, `L` is Galois over the
decomposition field).
-/

namespace Langlands.NYLL.RamificationTheory

universe u v

namespace HilbertRamification
namespace ValuationSubring

/-- Statement target for NYLL M239.004 `residueAction_ker`: the inertia group
is the kernel of the residue action. -/
def residueAction_kerStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    MonoidHom.ker (residueAction K A) = inertiaGroup K A

/-- Statement target for the NYLL M239.005 instance `inertiaGroup_normal`:
the inertia group is a normal subgroup of the decomposition group. -/
abbrev inertiaGroup_normalStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (A : _root_.ValuationSubring L),
    (inertiaGroup K A).Normal

/-- Statement target for the NYLL M239.038 instance
`decompositionField_isGalois`: for a finite-dimensional extension `L / K`,
`L` is Galois over the decomposition field `Z_w`. -/
abbrev decompositionField_isGaloisStatement : Prop :=
  ∀ (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (A : _root_.ValuationSubring L),
    IsGalois (decompositionField K A) L

end ValuationSubring
end HilbertRamification

end Langlands.NYLL.RamificationTheory
