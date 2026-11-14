/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.Invariants.U001.Definitions

/-!
# Norm images in degree-zero Tate cohomology of units: data

Modified by Worker 5454: extract M095.001 `CyclicCohomology.unitsNormLinearMap`
(lines 31–34) and M095.008 `CyclicCohomology.additiveNormSubgroup`
(lines 118–121) from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/TateH0/NormImage.lean` and prefix the namespace
with `Langlands.NYLL`. The source's two Mathlib imports are kept. Its NYLL
imports of `NormQuotient` and `TateH0.Invariants` are replaced by the
published M093.001 module (`localNormSubgroup`) and the M094.001 module of
this port; its NYLL import of `Cyclic.TateComparison` is not needed and is
dropped. The source's `open CategoryTheory` is omitted because neither
construction uses it. The constructions, universe `u` and parameter
telescopes are unchanged. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

/-- The group-cohomological norm endomorphism on the actual unit representation. -/
def unitsNormLinearMap (K L : Type) [Field K] [Field L] [Algebra K L]
    [Fintype Gal(L/K)] : Additive Lˣ →ₗ[ℤ] Additive Lˣ :=
  (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap

/-- The additive subgroup of `Additive Kˣ` attached to the multiplicative norm subgroup. -/
def additiveNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (Additive Kˣ) :=
  (localNormSubgroup K L).toAddSubgroup

end

end Langlands.NYLL.CyclicCohomology
