/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Prime.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: a zero prime-norm class is the norm of a prime power times a unit

Modified by Worker 5264, 15 November 2026: state the source theorem M083.002
`ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source import by focused published imports, omit
the proof, the rest of the source file and the unused
`open CategoryTheory`, and turn off the unused-variable linter for the
hypotheses `hTot`, `hSigmaResidue`, `hpiS`, `hpiL` and `hclass`, which the
proposition does not mention. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- Target: the representative extracted from a zero prime-norm class can be
written as `π_L^k v` with an actual unit `v ∈ U_L`.  This is the
prime/valuation calculation: both `L / K` and the Frobenius fixed field
`Σ / K` have relative residue degree one. -/
def primeNormClass_eq_zero_exists_unit_norm_eqStatement
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (DegreeData.AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field hLK)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field S.field hSK)]
    (hSigmaResidue :
      ((DegreeData.FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) : Prop :=
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS)

end ValuationData

end

end Langlands.NYLL.ClassFormation
