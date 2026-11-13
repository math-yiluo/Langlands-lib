/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the asserted type of M283.005
valuationSubring_mem_iff_of_separableClosureRingEquiv from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/AmbientPrimeNormTransport.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and package all thirty-one original binders inside a closed Prop-valued
definition with the suffix Statement, preserving their order, binder kinds
and the source's universe-zero field types. The two hypotheses hpsi and
hphi, which the conclusion does not mention, become unnamed implication
premises in their source positions. Replace the source imports by the
published module defining localSeparableValuationSubring and Mathlib's
valuation-extension module. Defer the truth proof; install no instance or
simp registration. Omit the original noncomputable section and all other
declarations of the module.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U006.Definitions

/-!
# Compatible field equivalences preserve valuation subrings: statement

A closed proposition saying that a ring equivalence between finite separable
extensions of two nonarchimedean local fields, compatible with embeddings
into the separable closures and with a ring equivalence of those separable
closures that matches their chosen valuation subrings, preserves membership
in the valuation subrings of the two extensions.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Compatible ring equivalences between finite extensions preserve
valuation-subring membership when their separable-closure transport preserves
the local valuation subrings. -/
def valuationSubring_mem_iff_of_separableClosureRingEquivStatement : Prop :=
  ∀ (F K L M : Type)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra F L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Valuation.HasExtension
      (ValuativeRel.valuation F) (ValuativeRel.valuation L)]
    [Field M] [ValuativeRel M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    [Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation M)]
    (jL : L →ₐ[F] SeparableClosure F)
    (jM : M →ₐ[K] SeparableClosure K)
    (psi : SeparableClosure F ≃+* SeparableClosure K),
    localSeparableValuationSubring F =
        (localSeparableValuationSubring K).comap psi.toRingHom →
      ∀ (phi : L ≃+* M),
        (∀ x : L, jM (phi x) = psi (jL x)) →
          ∀ (x : L),
            x ∈ (ValuativeRel.valuation L).valuationSubring ↔
              phi x ∈ (ValuativeRel.valuation M).valuationSubring

end Langlands.NYLL.LocalClassFieldTheory
