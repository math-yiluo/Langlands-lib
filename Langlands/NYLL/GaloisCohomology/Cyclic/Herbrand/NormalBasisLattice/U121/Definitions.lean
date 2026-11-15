/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U103.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.U106.Proofs

/-!
# The map from principal units to the successive lattice quotient

Modified by Worker 5264, 15 November 2026: port the source definition M144.121
`chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 with its source binders, section
variables, docstring and body. Prefix the namespace with `Langlands.NYLL`,
import the two published modules proving M144.103 and M144.106 instead of the
three source imports, and omit the other source declarations. In the proof
of `map_one'`, the source rewrite with
`chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff` is made with a local
hypothesis `hzero_iff` holding exactly that equivalence, because the
published theorem has a Prop-valued Statement type, which `rw` cannot use
directly. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/


universe u

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

/-- The map `u ↦ u - 1` from a subgroup `Vn = V^n` to the additive
successive quotient, viewed multiplicatively on the target. -/
def chosenNormalBasisPrincipalUnitToLatticeSuccQuotHom (n : Nat)
    {Vn : Subgroup 𝒪[L]ˣ}
    (hVn : (Vn : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L)) :
    Vn →* Multiplicative (chosenNormalBasisLatticeSuccQuot K L n) where
  toFun u :=
    Multiplicative.ofAdd
      (chosenNormalBasisPrincipalUnitLatticeClass K L n (u : 𝒪[L]ˣ)
        (by
          exact hVn ▸ u.2))
  map_one' := by
    change chosenNormalBasisPrincipalUnitLatticeClass K L n
      (1 : 𝒪[L]ˣ) (by exact hVn ▸ (1 : Vn).2) = 0
    have hzero_iff : ∀ (w : 𝒪[L]ˣ) (hw : w ∈ chosenNormalBasisPrincipalUnitSet K L n),
        chosenNormalBasisPrincipalUnitLatticeClass K L n w hw = 0 ↔
          w ∈ chosenNormalBasisPrincipalUnitSet K L (n + 1) :=
      fun w hw => chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff K L w hw
    rw [hzero_iff]
    change ((((1 : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) ∈
      chosenBaseUniformizerPowSubmodule K L (n + 1) (chosenNormalBasisIntegerLattice K L)
    rw [Units.val_one, sub_self, ZeroMemClass.coe_zero]
    exact Submodule.zero_mem _
  map_mul' := by
    intro u v
    have hu : (u : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ u.2
    have hv : (v : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ v.2
    have huv : ((u * v : Vn) : 𝒪[L]ˣ) ∈ chosenNormalBasisPrincipalUnitSet K L n := by
      exact hVn ▸ (u * v).2
    have hclass :=
      chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add
        (K := K) (L := L) hmul_error (u : 𝒪[L]ˣ) (v : 𝒪[L]ˣ) hu hv huv
    simpa using congrArg Multiplicative.ofAdd hclass

end

end Langlands.NYLL.CyclicCohomology
