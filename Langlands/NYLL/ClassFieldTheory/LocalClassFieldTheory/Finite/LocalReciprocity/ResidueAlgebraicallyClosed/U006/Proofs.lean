/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 172, 14 November 2026 UTC:
Extract the proof of M237.006,
valuationSubring_comap_residueField_isPurelyInseparable, from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean
(section binders line 83, theorem lines 148-216) at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace by
Langlands.NYLL. State the theorem as the published target
valuationSubring_comap_residueField_isPurelyInseparableStatement (F := F) A
and unfold it first. M237.005 (valuationSubringComapResidueMap_residue) is
not ported: add a local equation hres, proved by Mathlib's
IsLocalRing.ResidueField.map_residue with the published
valuationSubringComapMap_isLocalHom as local instance, and rewrite with
hres where the source rewrites with that lemma (two places). The rest of the
tactic proof is the source proof unchanged. Import the published U004
statement module instead of the source's imports.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
Submitted by Worker 106, 15 November 2026 UTC, from Worker 172's public
draft for Task 6927; the Lean code is unchanged from that draft.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicallyClosed.U004.Statements

/-!
# Proof: residue fields of a purely inseparable extension

Proof of the M237.006 target
`valuationSubring_comap_residueField_isPurelyInseparableStatement`.
See the paired Markdown for the source map and the proof outline.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- A purely inseparable extension remains purely inseparable after passing
to the residue fields of a valuation ring and its pullback.  In positive
characteristic this is the same Frobenius-power argument; in characteristic
zero the ambient purely inseparable extension is already trivial. -/
theorem valuationSubring_comap_residueField_isPurelyInseparable
    [IsPurelyInseparable F Omega] (A : ValuationSubring Omega) :
    valuationSubring_comap_residueField_isPurelyInseparableStatement (F := F) A := by
  unfold valuationSubring_comap_residueField_isPurelyInseparableStatement
  -- M237.005, reused from Mathlib (the source cites its own simp lemma).
  have hres : ∀ x : A.comap (algebraMap F Omega),
      valuationSubringComapResidueMap (F := F) A
          (IsLocalRing.residue (A.comap (algebraMap F Omega)) x) =
        IsLocalRing.residue A (valuationSubringComapMap (F := F) A x) := by
    have : IsLocalHom (valuationSubringComapMap (F := F) A) :=
      valuationSubringComapMap_isLocalHom (F := F) A
    exact IsLocalRing.ResidueField.map_residue (valuationSubringComapMap (F := F) A)
  let B := A.comap (algebraMap F Omega)
  let barI := valuationSubringComapResidueMap (F := F) A
  let : Algebra (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField A) := barI.toAlgebra
  obtain ⟨q, hqF⟩ := ExpChar.exists F
  let : ExpChar F q := hqF
  cases hqF with
  | zero =>
      let : Algebra.IsSeparable F Omega := inferInstance
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B)
        (ringExpChar (IsLocalRing.ResidueField B))]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨z, hz⟩ :=
        IsPurelyInseparable.surjective_algebraMap_of_isSeparable F Omega
          (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact a.property⟩
      refine ⟨0, IsLocalRing.residue B zB, ?_⟩
      simp only [pow_zero, pow_one]
      change barI (IsLocalRing.residue B zB) = IsLocalRing.residue A a
      dsimp only [barI, B]
      rw [hres]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz
  | prime hq =>
      let : CharP Omega q :=
        charP_of_injective_algebraMap (algebraMap F Omega).injective q
      let : CharP A q := A.subtype.charP A.subtype_injective q
      let : CharP (IsLocalRing.ResidueField A) q :=
        CharP.of_ringHom_of_ne_zero (IsLocalRing.residue A) q hq.ne_zero
      let : CharP (IsLocalRing.ResidueField B) q :=
        barI.charP barI.injective q
      let : ExpChar (IsLocalRing.ResidueField B) q := ExpChar.prime hq
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B) q]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact pow_mem a.property _⟩
      refine ⟨n, IsLocalRing.residue B zB, ?_⟩
      change barI (IsLocalRing.residue B zB) =
        (IsLocalRing.residue A a) ^ q ^ n
      dsimp only [barI, B]
      rw [hres]
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz

end PurelyInseparableComap

end
end Langlands.NYLL.LocalClassFieldTheory
