/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U005.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U006.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U008.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U066.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U068.Proofs

/-!
# NYLL M118.004: the Herbrand quotient of a finite module is one

Modified by Worker 5264, 15 November 2026: prove the published target
`herbrandQuotient_finite_module_eq_oneStatement` (M118.004) by the source
proof of `herbrandQuotient_finite_module_eq_one` in
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type and
begin the proof with `show` stating it unfolded. The source proof applies
M118.003 `herbrandQuotient_eq_one_of_card_eq`, whose proof is not in the
Library; the port proves it, with its source statement and source proof, as
the private theorem `herbrandQuotient_eq_one_of_card_eq_aux`. The source proof applies the unpublished M113.109
`herbrand_finite_module_card_eq`; the port proves it, with its source
statement and source proof, as a private theorem, together with the
unpublished source theorems its proof uses (M113.024-.027, M113.067,
M113.069, M113.107 and M113.108 of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`),
all under private `..._aux` names and with their source `omit` clauses; their
proofs use the published M113.005, M113.006, M113.008, M113.066 and M113.068
proofs, which the module imports. In the copy of M113.024 the source
argument `by simpa using ha`, which relies on the unpublished simp lemma
M113.019 `sigmaMinusOneHom_apply`, is replaced by `MonoidHom.mem_ker.mp ha`,
accepted because `sigmaMinusOneHom σ a` is `sigmaMinusOne G A σ a` by
definition.
Replace the source imports by the published statement module and these
published proof modules, and omit the rest of the source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.024 `sigmaMinusOneHom_ker_eq_fixedSubgroup` with
its source proof, under a private name. -/
private theorem sigmaMinusOneHom_ker_eq_fixedSubgroup_aux
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) :
    MonoidHom.ker (sigmaMinusOneHom (G := G) (A := A) σ) = fixedSubgroup G A := by
  ext a
  constructor
  · intro ha
    exact fixed_of_forall_mem_zpowers_of_sigmaMinusOne_eq_one
      (G := G) (A := A) (σ := σ) hgen (MonoidHom.mem_ker.mp ha)
  · intro ha
    change sigmaMinusOne G A σ a = 1
    simp [sigmaMinusOne, ha σ]

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.025
`card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup` with its source
proof, under a private name. -/
private theorem card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup_aux
    [Finite A] :
    Nat.card A = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [normKernelSubgroup, tateNormSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range (tateNormHom (G := G) (A := A))

omit [Fintype G] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.026
`card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup` with its source
proof, under a private name. -/
private theorem card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup_aux
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card A = Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) := by
  simpa [sigmaMinusOneHom_ker_eq_fixedSubgroup_aux (G := G) (A := A) σ hgen,
    augmentationSubgroup] using
    monoidHom_card_eq_card_ker_mul_card_range
      (sigmaMinusOneHom (G := G) (A := A) σ)

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.027 `herbrand_finite_module_cardinality_balance`
with its source proof, under a private name. -/
private theorem herbrand_finite_module_cardinality_balance_aux
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) =
      Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A) := by
  rw [← card_eq_card_fixedSubgroup_mul_card_augmentationSubgroup_aux
      (G := G) (A := A) σ hgen,
    ← card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroup_aux (G := G) (A := A)]

/-- The source theorem M113.067 `augmentationSubgroup_le_normKernelSubgroup`
with its source proof, under a private name. -/
private theorem augmentationSubgroup_le_normKernelSubgroup_aux (σ : G) :
    augmentationSubgroup G A σ ≤ normKernelSubgroup G A := by
  intro a ha
  rcases ha with ⟨b, rfl⟩
  exact tateNorm_sigmaMinusOne_eq_one (G := G) (A := A) σ b

/-- The source theorem M113.069 `tateNormSubgroup_le_fixedSubgroup` with its
source proof, under a private name. -/
private theorem tateNormSubgroup_le_fixedSubgroup_aux :
    tateNormSubgroup G A ≤ fixedSubgroup G A := by
  intro a ha g
  rcases ha with ⟨b, rfl⟩
  exact smul_tateNorm_eq (G := G) (A := A) g b

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.107
`card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup` with its
source proof, under a private name. -/
private theorem card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup_aux
    [Finite A] :
    Nat.card (fixedSubgroup G A) =
      Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A) := by
  simpa [HerbrandH0,
    card_subgroupOf_eq_card (tateNormSubgroup_le_fixedSubgroup_aux (G := G) (A := A))] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.108
`card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup`
with its source proof, under a private name. -/
private theorem card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup_aux
    (σ : G) [Finite A] :
    Nat.card (normKernelSubgroup G A) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (augmentationSubgroup G A σ) := by
  simpa [HerbrandHMinusOne,
    card_subgroupOf_eq_card
      (augmentationSubgroup_le_normKernelSubgroup_aux (G := G) (A := A) σ)] using
    (Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)))

omit [CommGroup B] [CommGroup C]
    [MulDistribMulAction G B] [MulDistribMulAction G C] in
/-- The source theorem M113.109 `herbrand_finite_module_card_eq` with its
source proof, under a private name. -/
private theorem herbrand_finite_module_card_eq_aux
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ) := by
  have h0 := card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroup_aux
    (G := G) (A := A)
  have hm :=
    card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroup_aux
      (G := G) (A := A) σ
  have hbal := herbrand_finite_module_cardinality_balance_aux
    (G := G) (A := A) σ hgen
  rw [h0, hm] at hbal
  have hfactor :
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) =
        Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
    calc
      Nat.card (HerbrandH0 G A) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ))
          =
          (Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A)) *
            Nat.card (augmentationSubgroup G A σ) := by
            ac_rfl
      _ = (Nat.card (HerbrandHMinusOne G A σ) *
            Nat.card (augmentationSubgroup G A σ)) *
            Nat.card (tateNormSubgroup G A) := hbal
      _ = Nat.card (HerbrandHMinusOne G A σ) *
          (Nat.card (tateNormSubgroup G A) * Nat.card (augmentationSubgroup G A σ)) := by
            ac_rfl
  have hNpos : 0 < Nat.card (tateNormSubgroup G A) :=
    Finite.card_pos (α := tateNormSubgroup G A)
  have hIpos : 0 < Nat.card (augmentationSubgroup G A σ) :=
    Finite.card_pos (α := augmentationSubgroup G A σ)
  exact Nat.mul_right_cancel (Nat.mul_pos hNpos hIpos) hfactor

/-- The source theorem M118.003 `herbrandQuotient_eq_one_of_card_eq` with its
source proof, under a private name. -/
private theorem herbrandQuotient_eq_one_of_card_eq_aux (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) :
    herbrandQuotient (G := G) (A := A) σ = 1 := by
  have hden : ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  unfold herbrandQuotient
  rw [hcard]
  exact div_self hden

/-- Herbrand-quotient theory Herbrand-quotient multiplicativity: the Herbrand quotient of a finite
cyclic module is `1`. -/
theorem herbrandQuotient_finite_module_eq_one
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] :
    herbrandQuotient_finite_module_eq_oneStatement (G := G) (A := A) σ hgen := by
  show herbrandQuotient (G := G) (A := A) σ = 1
  exact herbrandQuotient_eq_one_of_card_eq_aux (G := G) (A := A) σ
    (herbrand_finite_module_card_eq_aux (G := G) (A := A) σ hgen)

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
