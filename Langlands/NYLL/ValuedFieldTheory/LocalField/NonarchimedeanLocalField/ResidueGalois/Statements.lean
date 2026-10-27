/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Definitions

/-!
# Residue evaluation and base-residue fixedness targets

Adapted by Worker 761 from NYLL M160.002 and M160.004 on 27 October 2026.
The namespace is prefixed by `Langlands.NYLL`; the two source theorem types
are packaged as closed proposition definitions over an arbitrary shared universe.
Only the published residue-field equivalence and Mathlib's residue-field and
valuation-extension interfaces are imported. No proof of either formula is
exported here. See the paired Markdown for correspondence and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The residue-field equivalence sends the residue class of an integer to the residue
class of its image under the integer-ring restriction. This is the closed statement
target for NYLL M160.002. -/
def GaloisGroupResidueFieldEquivOfIsIntegralClosureResidueStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L]
        (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x)

/-- The residue-field equivalence fixes the image of the base residue field under the
canonical residue algebra map. This is the closed statement target for NYLL M160.004. -/
def GaloisGroupResidueFieldEquivOfIsIntegralClosureAlgebraMapStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝓀[K]),
    galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ (algebraMap 𝓀[K] 𝓀[L] x) =
      algebraMap 𝓀[K] 𝓀[L] x

end Langlands.NYLL.LocalFieldTheory
