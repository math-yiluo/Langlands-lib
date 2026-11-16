/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 750, 16 November 2026: extract the proof of M147.013 from
Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean at
fbd320cd8b1b06487c58227e92eb135794267709, lines 213–240. Add the
Langlands.NYLL namespace prefix and give the theorem the published target
applied to its parameters as its type. The source uses M147.012 for the
inclusion of the range in the kernel and M147.011 for the converse, whose
proofs are not yet in the Library: this proof replaces both uses by the
definitional evaluation of the maps on representatives (`change` and `rfl`),
taking representatives with the published `principalUnitsSuccQuotMk_surjective`
and `IntegerUnitsModPrincipalUnitsAtLevel.inductionOn`. The source `simpa`
step is replaced by `change`. Import the target module and these published
proofs instead of the source imports. Omit the source noncomputable section
and all other source declarations. See the paired Markdown; the original
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower.Maps.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.U007.Proofs
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients.U040.Proofs

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Exactness of `U_K^n/U_K^(n+1) → 𝒪_Kˣ/U_K^(n+1) → 𝒪_Kˣ/U_K^n`
at the middle finite-filtration quotient. -/
theorem principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_ker
    (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
    principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement K n := by
  unfold principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc_range_eq_kerStatement
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨u, rfl⟩ := principalUnitsSuccQuotMk_surjective K n x
    rw [MonoidHom.mem_ker]
    change integerUnitsModPrincipalUnitsAtLevelMk K n (u : 𝒪[K]ˣ) = 1
    exact (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n (u : 𝒪[K]ˣ)).2 u.2
  · intro hq
    revert hq
    refine IntegerUnitsModPrincipalUnitsAtLevel.inductionOn (n + 1)
      (motive := fun q =>
        q ∈ MonoidHom.ker (integerUnitsModPrincipalUnitsSuccMap K n) →
          q ∈ MonoidHom.range
            (principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc K n))
      q ?_
    intro x hq
    rw [MonoidHom.mem_ker] at hq
    change integerUnitsModPrincipalUnitsAtLevelMk K n x = 1 at hq
    have hx : x ∈ principalUnits K n :=
      (integerUnitsModPrincipalUnitsAtLevelMk_eq_one_iff K n x).1 hq
    let u : principalUnits K n := ⟨x, hx⟩
    exact ⟨principalUnitsSuccQuotMk K n u, rfl⟩

end Langlands.NYLL.CyclicCohomology
