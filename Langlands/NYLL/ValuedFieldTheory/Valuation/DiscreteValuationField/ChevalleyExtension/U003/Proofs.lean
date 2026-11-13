/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 133 (2026-11-13): extract only the proof of M110.003 from
Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ChevalleyExtension.lean
(lines 86–112) at commit fbd320cd8b1b06487c58227e92eb135794267709 into
Langlands.NYLL; import only the published ValuationSubringStatements module
of Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
and state the theorem as that module's `exists_extension_valuationSubringStatement`
applied to the source binders, opening it with `unfold` before the
unchanged source tactic proof. Because the M110.002 proof is not yet
in the Library, its source proof (lines 47–85) is reproduced here as the
private theorem mem_base_valuationSubring_of_lift_mem_aux, whose type is the
source conclusion of M110.002, and the source call at line 102 uses it. The
unused source universes x y z, the noncomputable section and the open
ResidueField namespace are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension.ValuationSubringStatements

/-!
# Chevalley's extension theorem in valuation-subring form (NYLL M110.003)

For an arbitrary field extension `L / K` and a valuation `vK` on `K`, there
is a valuation subring `B` of `L` that locally dominates the valuation ring of
`vK` and whose pullback to `K` is exactly that valuation ring.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {ΓK : Type w} [LinearOrderedCommGroupWithZero ΓK]

/-- Local copy of the source proof of M110.002 (source lines 47–85), kept
private so that it does not duplicate the public adapted name. -/
private theorem mem_base_valuationSubring_of_lift_mem_aux
    (vK : _root_.Valuation K ΓK)
    (B : ValuationSubring L)
    (hB : ∀ x : vK.valuationSubring, algebraMap vK.valuationSubring L x ∈ B.toSubring)
    (hlocal : IsLocalHom
      ((algebraMap vK.valuationSubring L).codRestrict B.toSubring hB))
    {x : K} (hxB : algebraMap K L x ∈ B.toSubring) :
    x ∈ vK.valuationSubring := by
  let A := vK.valuationSubring
  rcases A.mem_or_inv_mem x with hxA | hxinvA
  · exact hxA
  · by_cases hx0 : x = 0
    · simp [hx0]
    let y : A := ⟨x⁻¹, hxinvA⟩
    let f : A →+* B.toSubring :=
      (algebraMap A L).codRestrict B.toSubring hB
    let : IsLocalHom f := by
      dsimp [f, A]
      exact hlocal
    have hfy_unit : IsUnit (f y) := by
      apply IsUnit.of_mul_eq_one (⟨algebraMap K L x, hxB⟩ : B.toSubring)
      ext
      change (algebraMap K L) (x⁻¹) * (algebraMap K L) x = 1
      rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    have hy_unit : IsUnit y := IsUnit.of_map f y hfy_unit
    have hy_val : A.valuation (x⁻¹) = 1 := by
      simpa [y] using (A.valuation_eq_one_iff y).1 hy_unit
    have hx_val : A.valuation x = 1 := by
      rw [← inv_inv x, map_inv₀, hy_val, inv_one]
    exact A.mem_of_valuation_le_one x hx_val.le

/-- Chevalley's theorem in valuation-subring form: a valuation subring of `L`
locally dominating the valuation ring of `vK`, whose pullback along `K → L` is
exactly that valuation ring. -/
theorem exists_extension_valuationSubring
    (vK : _root_.Valuation K ΓK) :
    exists_extension_valuationSubringStatement (L := L) vK := by
  unfold exists_extension_valuationSubringStatement
  obtain ⟨B, hB, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing
      (f := algebraMap vK.valuationSubring L)
  refine ⟨B, hB, hlocal, ?_⟩
  intro x
  constructor
  · intro hxB
    exact mem_base_valuationSubring_of_lift_mem_aux vK B hB hlocal hxB
  · intro hxA
    have hxB :
        algebraMap vK.valuationSubring L
            (⟨x, hxA⟩ : vK.valuationSubring) ∈ B.toSubring :=
      hB ⟨x, hxA⟩
    rw [IsScalarTower.algebraMap_apply vK.valuationSubring K L] at hxB
    simpa using hxB

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation
