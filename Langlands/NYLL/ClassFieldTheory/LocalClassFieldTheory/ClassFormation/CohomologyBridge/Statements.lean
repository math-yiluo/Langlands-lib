/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.TateH0.NormImage.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Definitions

/-!
# The class-formation cohomology bridge: norm and coboundary targets

Modified by Worker 5454: extract the asserted types of M114.001
`LocalClassFieldTheory.unitsNormLinearMap_toMul_eq_tateNorm` (lines 35–40) and
M114.017 `LocalClassFieldTheory.unitsRhoSub_toMul_eq_sigmaMinusOne`
(lines 258–263) from the pinned NYLL
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean`
as Prop-valued definitions. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to each theorem name, keep the section variables of source line 33
verbatim (both theorems use all of them) followed by each theorem's own
parameters, and omit the proofs. The imports are the M095 data module of this
port (`unitsNormLinearMap`) and the published M113 data module (`tateNorm`,
`sigmaMinusOne`). See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open CyclicCohomology

noncomputable section

open scoped BigOperators

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CategoryTheory

variable (K L : Type) [Field K] [Field L] [Algebra K L]

/-- The norm in the actual unit representation is the multiplicative Herbrand
norm after passing from `Additive Lˣ` back to `Lˣ`. -/
def unitsNormLinearMap_toMul_eq_tateNormStatement
    [Fintype (Gal(L/K))] (x : Lˣ) : Prop :=
  Additive.toMul (unitsNormLinearMap K L (Additive.ofMul x)) =
    tateNorm (Gal(L / K)) Lˣ x

/-- Subtraction by the identity in the actual unit representation is the
multiplicative coboundary `x ↦ g•x/x`. -/
def unitsRhoSub_toMul_eq_sigmaMinusOneStatement
    (g : Gal(L/K)) (x : Lˣ) : Prop :=
  (Additive.toMul ((Rep.ofAlgebraAutOnUnits K L).ρ g (Additive.ofMul x)) : Lˣ) * x⁻¹ =
    sigmaMinusOne (Gal(L / K)) Lˣ g x

end

end Langlands.NYLL.LocalClassFieldTheory
