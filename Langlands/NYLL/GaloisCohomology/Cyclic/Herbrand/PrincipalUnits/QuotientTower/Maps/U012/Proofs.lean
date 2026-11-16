/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M147.012 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 191–212. Add the
Langlands.NYLL namespace prefix and give the theorem the published target
applied to its parameters as its type. The source eliminates the class with
M132.007 `PrincipalUnitsSuccQuot.inductionOn` and rewrites with M147.011 and
M147.004, whose proofs are not yet in the Library: this proof instead takes a
representative with the published `principalUnitsSuccQuotMk_surjective` and
evaluates the composite on it by `change`, which is definitional. The source
rewrite with `integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff` is made by
applying the reverse direction of that published theorem, which the target
module already imports. Import the target module and the published proof of
`principalUnitsSuccQuotMk_surjective` instead of the source imports. Omit the source
noncomputable section and all other source declarations. See the paired
Markdown; the original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U040.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The principal-unit inclusion followed by the successor map is the canonical
quotient map. -/
theorem integerUnitsSuccMap_comp_principalUnitsSuccQuot
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement K n := by
  unfold integerUnitsSuccMap_comp_principalUnitsSuccQuotStatement
  ext q
  obtain ⟨u, rfl⟩ := principalUnitsSuccQuotMk_surjective K n q
  rw [MonoidHom.comp_apply, MonoidHom.one_apply]
  change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
  exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n (u : 𝒪[K]ˣ)).2 u.2

end Langlands.NYLL.CyclicCohomology
