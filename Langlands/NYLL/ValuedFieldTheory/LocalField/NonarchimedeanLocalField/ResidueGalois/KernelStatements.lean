/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.AlgebraDefinitions

/-!
# Residue-kernel characterization targets

Adapted by Worker 84 from NYLL M160.017 and M160.018 on 29 October 2026.
The namespace is prefixed by `Langlands.NYLL`; the two source theorem types
are packaged as closed proposition definitions over an arbitrary shared universe.
The maps are the published residue algebra homomorphism and integer-ring restriction.
Neither characterization is proved here. See the paired Markdown for source
correspondence, hypotheses, notation and modifications.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Closed target for NYLL M160.017: membership in the residue kernel is equivalent
to equality of the residues of every integer and its conjugate. -/
def GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffResidueEqStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)),
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      ∀ x : 𝒪[L],
        IsLocalRing.residue 𝒪[L]
            (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x) =
          IsLocalRing.residue 𝒪[L] x

/-- Closed target for NYLL M160.018: membership in the residue kernel is equivalent
to every conjugate difference lying in the actual maximal ideal. -/
def GaloisGroupResidueAlgEquivHomOfIsIntegralClosureMemKerIffSubMemMaximalIdealStatement :
    Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)),
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      ∀ x : 𝒪[L],
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x ∈
          (𝓂[L] : Ideal 𝒪[L])

end Langlands.NYLL.LocalFieldTheory
