/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted the three source local
instances LocalClassFieldTheory.localAbstractFixedResidueIntermediateFieldAlgebra,
localAbstractFixedResidueIntermediateFieldSMul and
localAbstractFixedResidueIntermediateFieldModule (inventory M250.002–M250.004)
under the reserved names Langlands.NYLL.PortInternal.M250.d002,
Langlands.NYLL.PortInternal.M250.d003 and Langlands.NYLL.PortInternal.M250.d004,
written with `_root_.` inside the source namespace. The two references of the
SMul and Module bodies to the Algebra instance use its new name, and d003 and
d004, which have no source docstring, get one. The section variables,
binders, types, the `local instance` scope, the d002 docstring and the bodies
are otherwise unchanged. The namespace is prefixed with Langlands.NYLL; the NYLL
imports are replaced by the published module defining
localAbstractFixedResidueIntermediateField; the opens of the unused namespaces
CyclicCohomology, ClassFormation, LocalFieldTheory and
Field.absoluteGaloisGroup and the unused `open scoped Pointwise ValuativeRel`
are omitted. All other source declarations are omitted. The retained license
and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U001.Definitions

/-!
# Local scalar instances on the residue subfield of a fixed field

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`,
lines 20–34 (namespace, opens and section variables) and 54–79 (inventory
M250.002–M250.004).

As in the source, the three instances are `local`: their instance attribute
ends with the section below and is not exported. A consumer that needs the
source scope installs them with
`attribute [local instance] Langlands.NYLL.PortInternal.M250.d002
Langlands.NYLL.PortInternal.M250.d003 Langlands.NYLL.PortInternal.M250.d004`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open RamificationTheory

noncomputable section

open HilbertRamification.ValuationSubring

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical scalar structure on the selected fixed residue field.
Naming these instances keeps typeclass search from unfolding the fixed-field
and residue-action constructions in finite-dimensionality statements. -/
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d002
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    Algebra
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  (localAbstractFixedResidueIntermediateField K H).algebra

/-- Source local instance `localAbstractFixedResidueIntermediateFieldSMul`:
the scalar action underlying `Langlands.NYLL.PortInternal.M250.d002`. -/
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d003
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    SMul
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toSMul _ _ _ _
    (Langlands.NYLL.PortInternal.M250.d002 K H)

/-- Source local instance `localAbstractFixedResidueIntermediateFieldModule`:
the module structure underlying `Langlands.NYLL.PortInternal.M250.d002`. -/
noncomputable local instance _root_.Langlands.NYLL.PortInternal.M250.d004
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))) :
    Module
      (decompositionResidueField K (localSeparableValuationSubring K))
      (localAbstractFixedResidueIntermediateField K H) :=
  @Algebra.toModule _ _ _ _
    (Langlands.NYLL.PortInternal.M250.d002 K H)

end

end Langlands.NYLL.LocalClassFieldTheory
