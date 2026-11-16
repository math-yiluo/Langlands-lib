/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract the targets M152.025 and M152.026,
-- prefix the namespace and narrow imports. See GaloisActionLawStatements.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_one_applyStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L 1 x = x

def galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv_mul_applyStatement
    (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (τ υ : Gal(L/K)) (x : chosenNormalBasisIntegerLattice K L) : Prop :=
    galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L (τ * υ) x =
      galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ
        (galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L υ x)

end

end Langlands.NYLL.LocalClassFieldTheory
