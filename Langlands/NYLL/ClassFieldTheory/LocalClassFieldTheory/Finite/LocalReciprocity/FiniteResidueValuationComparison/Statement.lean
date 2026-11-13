/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 122 (2026-11-13): extract the statement of
   M251.001 LocalClassFieldTheory.ValuationSubring.restrictIntermediateField_eq_of_finite_separable
   (lines 37-44) of
   Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueValuationComparison.lean
   from upstream commit fbd320cd8b1b06487c58227e92eb135794267709, with the
   ambient namespace and universes at lines 21-31. Omit the proof. Close the
   source telescope, with its binder kinds, inside a new Prop-valued
   definition named by the source theorem name with suffix Statement; name
   the source's auto-bound value-group universe of `CompleteDVF K` as `w`.
   Prefix the namespace with Langlands.NYLL, state it for the Library's
   published CompleteDVF and M233.004 restrictIntermediateField, and replace
   the upstream imports by those two modules and focused Mathlib imports.
   The original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteLevelValuationRestriction.RestrictIntermediateField
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Valuation.Extension

/-!
# Finite-separable comparison of restricted valuation rings: statement

Closed proposition for the NYLL theorem M251.001: over a complete discrete
valuation field `K`, the restriction of an extension valuation ring of an
ambient field `Omega` to a finite separable intermediate field `E` equals
every extension valuation ring of `E`. This module states it without proving
it.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ValuationTheory RamificationTheory

open DiscreteValuationField

/-- M251.001, `ValuationSubring.restrictIntermediateField_eq_of_finite_separable`:
over a complete discrete valuation field `base` on `K`, restricting a
valuation subring `A` of `Omega` whose valuation extends `base` to a finite
separable intermediate field `E` gives every valuation subring `C` of `E`
whose valuation extends `base`. -/
def ValuationSubring.restrictIntermediateField_eq_of_finite_separableStatement.{u, v, w} :
    Prop :=
  ∀ {K : Type u} {Omega : Type v} [Field K] [Field Omega] [Algebra K Omega]
    (base : CompleteDVF.{u, w} K)
    (A : _root_.ValuationSubring Omega)
    [_root_.Valuation.HasExtension base.valuation A.valuation]
    (E : IntermediateField K Omega) [FiniteDimensional K E]
    [Algebra.IsSeparable K E]
    (C : _root_.ValuationSubring E)
    [_root_.Valuation.HasExtension base.valuation C.valuation],
    A.restrictIntermediateField E = C

end Langlands.NYLL.LocalClassFieldTheory
