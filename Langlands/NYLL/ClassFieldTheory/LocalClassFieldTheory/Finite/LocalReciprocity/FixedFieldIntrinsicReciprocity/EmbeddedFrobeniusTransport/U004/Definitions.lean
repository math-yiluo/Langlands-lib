/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 57, 14 November 2026:
Port the definition intrinsicBaseContinuousEquivAmbientEmbeddedField (M281.004)
from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldIntrinsicReciprocity/EmbeddedFrobeniusTransport.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL namespace
prefix and import the published proof module of
intrinsicBaseEquivAmbientEmbeddedField_continuous (M281.003) instead of the
source imports. Keep only the open line that this definition needs. Omit all
other declarations of the source file.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.EmbeddedFrobeniusTransport.U003.Proofs

/-!
# The embedded intrinsic-to-ambient base equivalence as a homeomorphism

The equivalence `intrinsicBaseEquivAmbientEmbeddedField K F i e` bundled as a
continuous multiplicative equivalence: its continuity is the published
theorem `intrinsicBaseEquivAmbientEmbeddedField_continuous`, and continuity
of the inverse follows from compactness of the domain and the Hausdorff
property of the codomain.
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open RamificationTheory

/-- Bundles the intrinsic-to-ambient absolute Galois equivalence as a continuous
multiplicative equivalence. -/
noncomputable def
    intrinsicBaseContinuousEquivAmbientEmbeddedField
    (K F : Type) [Field K] [Field F]
    [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (i : F →ₐ[K] SeparableClosure K) :
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    (e : SeparableClosure F ≃ₐ[F] SeparableClosure K) →
      (intrinsicAbstractBase F).toSubgroup ≃ₜ*
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup := by
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hpsi : Continuous psi :=
    intrinsicBaseEquivAmbientEmbeddedField_continuous
      K F i e
  letI : CompactSpace (intrinsicAbstractBase F).toSubgroup :=
    isCompact_iff_compactSpace.mp
      ((intrinsicAbstractBase F).isClosed'.isCompact)
  exact
    { toMulEquiv := psi
      continuous_toFun := hpsi
      continuous_invFun :=
        hpsi.continuous_symm_of_equiv_compact_to_t2 }

end Langlands.NYLL.LocalClassFieldTheory
