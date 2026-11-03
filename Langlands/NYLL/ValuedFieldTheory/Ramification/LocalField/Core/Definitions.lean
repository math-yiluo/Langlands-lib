/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1237, 2026-11-03, with source/interface extraction,
witness design and reuse analysis contributed by Worker 106:
isolate M327.004 and M327.005 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL and import the focused published modules. Replace the
global M248.008 extension instance by a local witness taken from the
published chosenLocalExtension_properties, and replace the M327.001
uniqueness alias by the published chosenLocalExtension_uniqueValuationExtension
at comparison universe 0. Retained license and notices: licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.Basic
import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenPropertiesProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.ChosenUniquenessProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.HerbrandFunction.Definitions

/-!
# Lower and upper ramification groups of a finite Galois local extension

This extracts exactly M327.004 and M327.005 from the pinned NYLL
`Ramification/LocalField/Core.lean`: the actual real lower and upper
ramification groups of a finite Galois extension of a nonarchimedean local
field, on the canonical base valuation and the named chosen valuation of the
extension.
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory.LocalField

open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.RamificationTheory.HilbertRamification

/-- The actual real lower ramification group of an arbitrary finite Galois
extension of nonarchimedean local fields, using its integral-closure
valuation. -/
noncomputable def localLowerRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  letI : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  Higher.lowerRamificationGroup
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) t

/-- The actual real upper ramification group of an arbitrary finite Galois
extension of nonarchimedean local fields. -/
noncomputable def localUpperRamificationGroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (t : ℝ) : Subgroup Gal(L / K) :=
  letI : _root_.Valuation.HasExtension (localCompleteDVF K).valuation
      (chosenLocalExtensionCompleteDVF K L).valuation :=
    Classical.choose (chosenLocalExtension_properties K L)
  Higher.upperRamificationGroupOfUniqueExtension
    (base := (localCompleteDVF K).toDVF)
    (target := (chosenLocalExtensionCompleteDVF K L).toDVF)
    (chosenLocalExtension_uniqueValuationExtension.{0} K L) t

end Langlands.NYLL.RamificationTheory.LocalField
