/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 15 November 2026:
Prove the published closed statement
Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement
of M274.007 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709, following the source proof.
Add the Langlands.NYLL namespace prefix. Import the module proving M274.006
(U006 Proofs), through which the M273.008 theorem
intrinsicBaseEquivAmbientEmbeddedField_apply_val is imported, and the
published M098.027 statement module (ConcreteReciprocityCanonical U027
Statements). Prove that M098.027 statement as a local have with the source
proof of finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
(and its private helper M098.026 as a nested local have), because the
Library does not yet prove it. Omit the source's local data EI, hRange, hJH,
hSourceNormal and hTargetNormal, which the proof does not use after the
statement's own local data is unfolded. Omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U006.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical.U027.Statements

/-!
# Embedded extension quotients: action of the equivalence on `E`

The proof of the published closed proposition that the automorphism of `E`
attached to the class of an ambient automorphism `rho` acts, after applying
the embedding `j`, as `rho` does.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory CyclicCohomology

/-- Evaluating the ambient embedded quotient class on an element of `E`
agrees, after applying the embedding, with the original ambient automorphism. -/
theorem ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply :
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_applyStatement := by
  intro K F E _ _ _ _ _ _ _ _ _ _ _ j
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e rho x
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun y => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let tau :
      (intrinsicAbstractBase F).toSubgroup :=
    psi.symm rho
  have hpsi : psi tau = rho :=
    psi.apply_symm_apply rho
  have hquotient :
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e (QuotientGroup.mk rho) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) := by
    rw [← hpsi]
    exact
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
        K F E j e tau
  rw [hquotient]
  have hmkApply :
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement := by
      intro K L _ _ _ _ _ i τ x
      have baseFixing_mk_apply :
          ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
            (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
            (τ : (closedFixingSubgroup K Ω
              (⊥ : IntermediateField K Ω)).toSubgroup) (x : E),
            E.val ((baseFixingExtensionQuotientEquivGaloisGroup K Ω E
              (QuotientGroup.mk τ)) x) = τ.1 (E.val x) := by
        intro K Ω _ _ _ _ E _ _ τ x
        have hq :
            baseFixingExtensionQuotientEquivAmbient K Ω E
                (QuotientGroup.mk τ) =
              QuotientGroup.mk' (closedFixingSubgroup K Ω E).toSubgroup τ.1 := by
          rfl
        have hn := InfiniteGalois.normalAutEquivQuotient_apply
          (closedFixingSubgroup K Ω E) τ.1
        change InfiniteGalois.normalAutEquivQuotient (closedFixingSubgroup K Ω E)
            (QuotientGroup.mk' _ τ.1) = _ at hn
        rw [baseFixingExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
          MulEquiv.trans_apply, hn, AlgEquiv.autCongr_apply]
        simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
          IntermediateField.equivOfEq_apply]
        change
          (((AlgEquiv.restrictNormalHom
            (IntermediateField.fixedField
              (closedFixingSubgroup K Ω E).toSubgroup) τ.1)
            ⟨E.val x, _⟩ : IntermediateField.fixedField
              (closedFixingSubgroup K Ω E).toSubgroup) : Ω) =
            τ.1 (E.val x)
        rw [AlgEquiv.restrictNormalHom_apply]
      let E := finiteGaloisFieldRangeOfEmbedding K L i
      let e := finiteGaloisFieldRangeEquivOfEmbedding K L i
      let g := baseFixingExtensionQuotientEquivGaloisGroup
        K (SeparableClosure K) E (QuotientGroup.mk τ)
      have hb := baseFixing_mk_apply
        K (SeparableClosure K) E τ (e x)
      have he (y : E) : i (e.symm y) = E.val y := by
        exact congrArg Subtype.val (e.apply_symm_apply y)
      change i (((e.autCongr).symm g) x) = τ.1 (i x)
      calc
        i (((e.autCongr).symm g) x) = E.val (g (e x)) := by
          simpa only [AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply,
            AlgEquiv.trans_apply, AlgEquiv.symm_symm] using he (g (e x))
        _ = τ.1 (E.val (e x)) := hb
        _ = τ.1 (i x) := rfl
  have haction :=
    hmkApply F E jI tau x
  calc
    j
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) x) =
        e (tau.1 (jI x)) := by
      rw [show
        j
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
              F E jI (QuotientGroup.mk tau) x) =
          e
            (jI
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x)) by
        change
          j
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x) =
            e
              (e.symm
                (j
                  (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                    F E jI (QuotientGroup.mk tau) x)))
        rw [e.apply_symm_apply]]
      exact congrArg e haction
    _ = (psi tau).1.1 (j x) := by
      rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val]
      rfl
    _ = rho.1.1 (j x) := by
      rw [hpsi]

end Langlands.NYLL.LocalClassFieldTheory
