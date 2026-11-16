/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueDatum.Initial.Statements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.U022.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U012.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U010.Proofs

/-!
# Finite local reciprocity: the degree image of a finite fixing subgroup (proof)

Adapted from NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 41–63 (the private
M238.002) and 65–107 (M238.003), with the section variables of lines 31–33.
Worker 59 proves the published target
`Langlands.NYLL.LocalClassFieldTheory.residueDatumIn_fieldImage_closedFixingSubgroupStatement`
under the source theorem name, prefixed the namespaces by `Langlands.NYLL`,
kept the private M238.002 as a private theorem of this module, supplied the
source's private instances `IsAlgClosure k Omega` (M236.002) and
`IsGalois k Omega` (M236.003) by local `have`s, added a `show` that unfolds the
target, and replaced the NYLL imports by the published modules whose theorems
the proof uses. The source proof script is otherwise unchanged. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open Langlands.NYLL.RamificationTheory

open Langlands.NYLL.ClassFormation

noncomputable section

variable (k Omega : Type)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [Fintype k] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega] in
private theorem mem_fixingSubgroup_iff_restrictNormalHom_eq_one
    (E : FiniteGaloisIntermediateField k Omega)
    (sigma : Omega ≃ₐ[k] Omega) :
    sigma ∈ E.toIntermediateField.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom E sigma = 1 := by
  constructor
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom E sigma x : E) : Omega) = (x : Omega)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hsigma x x.property
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : E := ⟨x, hx⟩
    have hy := congrArg (fun tau : E ≃ₐ[k] E => tau y) hsigma
    have hyval := congrArg Subtype.val hy
    rw [AlgEquiv.restrictNormalHom_apply] at hyval
    simpa [y] using hyval

/-- The degree image of the subgroup fixing a finite residue extension of
degree `n` is exactly `n ℤ̂`. -/
theorem residueDatumIn_fieldImage_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    residueDatumIn_fieldImage_closedFixingSubgroupStatement k Omega E := by
  have : IsAlgClosure k Omega := ⟨inferInstance, inferInstance⟩
  have : IsGalois k Omega := {}
  show (residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E) =
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range.toSubgroup
  ext z
  let : Finite E := Module.finite_of_finite k
  constructor
  · rintro ⟨sigma, rfl⟩
    change (residueAbsoluteDegreeIn k Omega sigma.1).toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos]
    change zHatReduction (Module.finrank k E) Module.finrank_pos
      (residueAbsoluteDegreeIn k Omega sigma.1).toAdd = 0
    have hrestrict : AlgEquiv.restrictNormalHom E sigma.1 = 1 :=
      (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E sigma.1).1 sigma.2
    have hcoordinate :=
      finiteResidueFrobeniusExponentEquiv_symm_restrict_in
        k Omega sigma.1 E
    unfold finiteResidueFrobeniusExponentEquiv_symm_restrict_inStatement
      at hcoordinate
    rw [hrestrict, map_one] at hcoordinate
    exact congrArg Multiplicative.toAdd hcoordinate |>.symm
  · intro hz
    change z.toAdd ∈
      (zHatMulNat (Module.finrank k E)).toAddMonoidHom.range at hz
    rw [zHatMulNat_range_eq_ker_reduction
      (Module.finrank k E) Module.finrank_pos] at hz
    refine ⟨⟨residueAbsoluteFrobenius k Omega z, ?_⟩, ?_⟩
    · apply (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E (residueAbsoluteFrobenius k Omega z)).2
      rw [restrictNormalHom_residueAbsoluteFrobenius]
      change finiteResidueFrobeniusFromZHat k E z = 1
      rw [finiteResidueFrobeniusFromZHat_apply]
      change finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd)) = 1
      rw [show zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd = 0
        from hz]
      exact map_one (finiteResidueFrobeniusExponentHom k E)
    · exact (residueAbsoluteFrobeniusEquivIn k Omega).symm_apply_apply z

end
end Langlands.NYLL.LocalClassFieldTheory
