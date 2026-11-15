/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Frobenius.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U013.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U006.Proofs
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Finite local reciprocity: surjectivity of Frobenius on a residue algebraic closure (proof)

Modified by Worker 5168: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement`
(M236.015) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks. The instances of the source's private
M236.002 (`IsAlgClosure k Omega`) and M236.003 (`IsGalois k Omega`) are
supplied by local `have`s, as in the target. The source proof rewrites with
M236.014. The needed M236.013 and M236.011 facts are proved locally,
and the pointwise Frobenius argument reuses the published M168.006 restriction
theorem. The remaining private lemmas follow the source arguments. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

section Galois

variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The element `1 ∈ ℤ̂` acts on every element by the arithmetic Frobenius
`x ↦ x ^ #k` (the pointwise content of M168.009). -/
private theorem u015_residueAbsoluteFrobenius_one_apply (x : Omega) :
    residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd (1 : ZHat)) x =
      x ^ Fintype.card k := by
  let E := FiniteGaloisIntermediateField.adjoin k ({x} : Set Omega)
  have hx : x ∈ E.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin k ({x} : Set Omega) rfl
  have hres := AlgEquiv.restrictNormalHom_apply E.toIntermediateField
    (residueAbsoluteFrobenius k Omega (Multiplicative.ofAdd (1 : ZHat))) ⟨x, hx⟩
  rw [restrictNormalHom_residueAbsoluteFrobenius k Omega _ E] at hres
  let : Finite E := Module.finite_of_finite k
  change ((finiteResidueFrobeniusFromZHat k E (Multiplicative.ofAdd (1 : ZHat))
    ⟨x, hx⟩ : E) : Omega) = _ at hres
  rw [finiteResidueFrobeniusFromZHat_one k E] at hres
  rw [← hres]
  simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rfl

end Galois

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega] in
/-- For a field `Omega` over the finite field `k`, an element fixed by
`x ↦ x ^ #k` lies in the image of `k` (the backward direction of M236.011). -/
private theorem u015_mem_range_algebraMap_of_pow_card
    (x : Omega) (hxpow : x ^ Fintype.card k = x) :
    x ∈ Set.range (algebraMap k Omega) := by
  let p : k[X] := X ^ Fintype.card k - X
  have hpne : p ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
  have hxroot : x ∈ p.rootSet Omega := by
    rw [Polynomial.mem_rootSet_of_ne hpne]
    simp [p, hxpow]
  have hsplits : (p.map (algebraMap k k)).Splits := by
    simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
  have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
  rw [← himage] at hxroot
  rcases hxroot with ⟨a, _ha, hax⟩
  exact ⟨a, hax⟩

/-- The intrinsic Frobenius homomorphism is surjective (M236.015). -/
theorem residueAbsoluteFrobenius_isAlgClosure_surjective :
    residueAbsoluteFrobenius_isAlgClosure_surjectiveStatement k Omega := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  show Function.Surjective (residueAbsoluteFrobenius k Omega)
  -- M236.013: the closed image fixes exactly the base field.
  have hfixed : IntermediateField.fixedField
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hmem : residueAbsoluteFrobenius k Omega
            (Multiplicative.ofAdd (1 : ZHat)) ∈
          (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup :=
        ⟨Multiplicative.ofAdd (1 : ZHat), rfl⟩
      rw [IntermediateField.mem_fixedField_iff] at hx
      have hxfix := hx _ hmem
      rw [u015_residueAbsoluteFrobenius_one_apply k Omega x] at hxfix
      rw [IntermediateField.mem_bot]
      exact u015_mem_range_algebraMap_of_pow_card k Omega x hxfix
    · exact bot_le
  -- M236.014: by infinite Galois theory the closed image is everything.
  have htop : (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤ := by
    have h := InfiniteGalois.fixingSubgroup_fixedField
      (residueAbsoluteFrobeniusRangeIn k Omega)
    rw [hfixed, IntermediateField.fixingSubgroup_bot] at h
    exact h.symm
  -- The source proof of M236.015.
  intro sigma
  have hsigma : sigma ∈
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup := by
    rw [htop]
    exact Subgroup.mem_top sigma
  exact hsigma

end
end Langlands.NYLL.LocalClassFieldTheory
