/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of the private theorem M276.004
abstractFixedFieldCosetToAlgHom_surjective from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709,
as the theorem Langlands.NYLL.PortInternal.M276.d004 proving the published
d004Statement. Introduce the statement's binders and then keep the source
tactic proof unchanged, with the published names opened.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements

/-!
# Relative cosets give every embedding of a finite fixed field: proof
-/

namespace Langlands.NYLL.PortInternal.M276

open Langlands.NYLL.LocalClassFieldTheory

/-- Every embedding of a finite upper fixed field into the separably closed
ambient field comes from a relative left coset (source unit M276.004). -/
theorem d004 : d004Statement := by
  intro k Ω _ _ _ _ _ K L hLK _ f
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  let : Algebra.IsSeparable (abstractRelativeFixedField k Ω hLK) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := abstractFixedField k Ω K)
      (L := abstractRelativeFixedField k Ω hLK)
      (M := Ω) (E := Ω)) f
  let σReal : Gal(Ω / abstractFixedField k Ω K) :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id (abstractFixedField k Ω K) Ω)).1
  let σ : K.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup k Ω K).symm σReal
  refine ⟨QuotientGroup.mk σ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg
    (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
      abstractFixedField k Ω K] Ω => ψ x) hφ
  change σReal (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

end Langlands.NYLL.PortInternal.M276
