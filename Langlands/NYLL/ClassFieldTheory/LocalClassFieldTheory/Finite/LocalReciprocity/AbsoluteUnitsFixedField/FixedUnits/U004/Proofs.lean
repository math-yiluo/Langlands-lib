/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 96, 13 November 2026 UTC:
Extract only the proof of M088.004 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only the published FixedUnits Statements module and
open only RamificationTheory and KummerTheory. State the theorem as the
published Statement applied to the source parameters. The source's opening
change and rewrite by KummerTheory.mem_ambientFixedAddSubgroup_iff, whose
source proof is Iff.rfl and which is not published, are replaced by one
change to the unfolded invariance condition. The rest of the proof is
unchanged. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements

/-!
# Galois-fixed ambient units

The proof that an ambient unit `x` of a Galois extension `Ω/K` is fixed by the
closed fixing subgroup of an intermediate field `E` exactly when its
underlying field element lies in `E`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory KummerTheory

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- An ambient unit is fixed by `Gal(Ω/E)` exactly when its underlying
field element belongs to `E`. -/
theorem mem_galoisAmbientUnits_fixed_iff
    (E : IntermediateField K Ω)
    (x : Additive Ωˣ) :
    mem_galoisAmbientUnits_fixed_iffStatement K Ω E x := by
  change
    (∀ h : (closedFixingSubgroup K Ω E).toSubgroup,
        (galoisAmbientUnitsRep K Ω).ρ h.1 x = x) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E
  constructor
  · intro hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup E,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσclosed :
        σ ∈ (closedFixingSubgroup K Ω E).toSubgroup := by
      simpa only [closedFixingSubgroup] using hσ
    have hfixed := hx ⟨σ, hσclosed⟩
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ σ x =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ] at hfixed
    have hval := congrArg
      (fun z : Additive Ωˣ ↦ ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    convert hval using 1
    rfl
  · intro hx σ
    have hσE : σ.1 ∈ E.fixingSubgroup := by
      simpa only [closedFixingSubgroup] using σ.2
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ
            (σ : Gal(Ω / K)) x =
          Additive.ofMul
            (Units.mapEquiv
              (σ : Gal(Ω / K)).toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    convert (IntermediateField.mem_fixingSubgroup_iff E σ.1).1 hσE _ hx using 1
    rfl

end Langlands.NYLL.LocalClassFieldTheory
