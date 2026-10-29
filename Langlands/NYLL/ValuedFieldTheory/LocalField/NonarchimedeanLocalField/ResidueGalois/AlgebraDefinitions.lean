/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois.Proofs

/-!
# Residue-field algebra automorphisms from an integral-closure restriction

Adapted by Worker 761 from NYLL M160.005 and M160.006 on 29 October 2026.
The namespace is prefixed by `Langlands.NYLL`; only these two data definitions are
retained. The group-law fields, which the source proves by `rfl` on residue
representatives, are proved from the published residue-representative evaluation
and the published forward evaluation of the integer-ring restriction.
See the paired Markdown for correspondence and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field equivalence induced by a field automorphism, as an algebra
automorphism over the base residue field. -/
@[implicit_reducible]
def galoisGroupResidueAlgEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] where
  __ := galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
  commutes' := galoisGroupResidueFieldEquivOfIsIntegralClosure_algebraMap K L σ

/-- The residue-field algebra automorphisms induced by field automorphisms, as a
group homomorphism. -/
def galoisGroupResidueAlgEquivHomOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] :
    Gal(L/K) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) where
  toFun := galoisGroupResidueAlgEquivOfIsIntegralClosure K L
  map_one' := by
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change galoisGroupResidueFieldEquivOfIsIntegralClosure K L 1
        (IsLocalRing.residue 𝒪[L] a) = IsLocalRing.residue 𝒪[L] a
    rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L 1 a]
    refine congrArg (IsLocalRing.residue 𝒪[L]) (Subtype.ext ?_)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L 1 a]
    exact AlgEquiv.one_apply (a : L)
  map_mul' σ τ := by
    refine AlgEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change galoisGroupResidueFieldEquivOfIsIntegralClosure K L (σ * τ)
        (IsLocalRing.residue 𝒪[L] a) =
      galoisGroupResidueFieldEquivOfIsIntegralClosure K L σ
        (galoisGroupResidueFieldEquivOfIsIntegralClosure K L τ
          (IsLocalRing.residue 𝒪[L] a))
    rw [galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L τ a,
      galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L σ,
      galoisGroupResidueFieldEquivOfIsIntegralClosure_residue K L (σ * τ) a]
    refine congrArg (IsLocalRing.residue 𝒪[L]) (Subtype.ext ?_)
    rw [galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L (σ * τ) a,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L σ,
      galoisGroupIntegerRingEquivOfIsIntegralClosure_apply K L τ a]
    exact AlgEquiv.mul_apply σ τ (a : L)

end

end Langlands.NYLL.LocalFieldTheory
