/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 122 (2026-11-13): extract the statements of
   M233.005 restrictIntermediateField_eq_comap (line 121),
   M233.006 mem_restrictIntermediateField_iff (line 127),
   M233.007 restrictIntermediateField_hasExtension (line 133) and
   M233.010 smul_hasExtension (line 172) of
   Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteLevelValuationRestriction.lean
   from upstream commit fbd320cd8b1b06487c58227e92eb135794267709, with the
   section variables at line 112 and `open scoped Pointwise` at line 150.
   Omit the proofs and the @[simp] attributes (deferred to the proofs).
   Close each source telescope, with its binder kinds, inside a new
   Prop-valued definition named by the source theorem name with suffix
   Statement; the two @[simp] rows M233.005 and M233.006 use `abbrev`, so
   that the simp attribute on their proofs gives usable rewrite rules.
   Qualify Mathlib's ValuationSubring and Valuation with _root_. Prefix the
   namespace with Langlands.NYLL and replace the upstream imports by the
   published M233.004 definition and one focused Mathlib import. The
   original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.RestrictIntermediateField
import Mathlib.RingTheory.Valuation.Extension

/-!
# Restricting valuation subrings to intermediate fields: statements

Closed propositions for the four NYLL theorems M233.005, M233.006, M233.007
and M233.010 about `restrictIntermediateField` and Galois translates of
valuation subrings. This module states them without proving them.
-/

namespace Langlands.NYLL.RamificationTheory

namespace ValuationSubring

/-- M233.005, `restrictIntermediateField_eq_comap`: the restriction of a
valuation subring of `Ω` to an intermediate field `E` is its preimage under
the inclusion `E → Ω`. -/
abbrev restrictIntermediateField_eq_comapStatement.{u, v} : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (A : _root_.ValuationSubring Ω) (E : IntermediateField K Ω),
    (restrictIntermediateField A E) = A.comap (algebraMap E Ω)

/-- M233.006, `mem_restrictIntermediateField_iff`: an element of `E` lies in
the restriction exactly when its image in `Ω` lies in the original valuation
subring. -/
abbrev mem_restrictIntermediateField_iffStatement.{u, v} : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    (A : _root_.ValuationSubring Ω) (E : IntermediateField K Ω) (x : E),
    x ∈ (restrictIntermediateField A E) ↔ (x : Ω) ∈ A

/-- M233.007, `restrictIntermediateField_hasExtension`: if the valuation of a
valuation subring `A` of `Ω` extends a valuation `v` of `K`, then so does the
valuation of its restriction to every intermediate field `E`. -/
def restrictIntermediateField_hasExtensionStatement.{u, v, w} : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : _root_.Valuation K Γ) (A : _root_.ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω),
    _root_.Valuation.HasExtension v ((restrictIntermediateField A E)).valuation

open scoped Pointwise in
/-- M233.010, `smul_hasExtension`: if the valuation of a valuation subring
`A` of `Ω` extends a valuation `v` of `K`, then so does the valuation of its
pointwise translate `σ • A` by every `K`-algebra automorphism `σ` of `Ω`. -/
def smul_hasExtensionStatement.{u, v, w} : Prop :=
  ∀ {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : _root_.Valuation K Γ) (A : _root_.ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω),
    _root_.Valuation.HasExtension v (σ • A).valuation

end ValuationSubring

end Langlands.NYLL.RamificationTheory
