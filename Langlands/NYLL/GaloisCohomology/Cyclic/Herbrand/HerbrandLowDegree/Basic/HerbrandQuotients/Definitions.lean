/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U011.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U012.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.U017.Proofs

/-!
# Low-degree Herbrand quotients: norm and `σ - 1` homomorphisms, subgroups and quotient groups

Modified by Worker 9: extract M113.013, M113.018, M113.021–M113.023,
M113.028–M113.035, M113.056, M113.057 and M113.059–M113.065 from the pinned
NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`
(lines 183–189, 219–225, 251–264, 315–386, 681–699 and 709–768), prefix the
namespace with `Langlands.NYLL`, and write the section-variable telescope that
each declaration includes after its `omit` (source lines 62–64) as explicit
binders in the same order and binder kinds. `tateNorm`, `sigmaMinusOne`,
`fixedSubgroup` and `rightRegularFunctionMulDistribMulAction` and the source's
nine Mathlib imports come from the published sibling `Basic.Definitions`
module; the `map_one'` and `map_mul'` fields of `tateNormHom` and the
`map_mul'` field of `sigmaMinusOneHom` cite the published proofs
`tateNorm_one`, `tateNorm_mul` and `sigmaMinusOne_mul` by name, as the source
does. The declarations, their universes, attributes and bodies, including
every proof field and tactic block, are otherwise unchanged. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- The finite-group norm as a multiplicative homomorphism. -/
def tateNormHom {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : A →* A where
  toFun := tateNorm G A
  map_one' := tateNorm_one (G := G) (A := A)
  map_mul' := tateNorm_mul (G := G) (A := A)

/-- The multiplicative coboundary `a ↦ a^(σ-1)` as a homomorphism. -/
def sigmaMinusOneHom {G : Type uG} {A : Type uA} [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) : A →* A where
  toFun := sigmaMinusOne G A σ
  map_one' := by simp [sigmaMinusOne, MulDistribMulAction.smul_one]
  map_mul' := sigmaMinusOne_mul (G := G) (A := A) σ

/-- Herbrand-quotient theory: the norm image `N_G A`. -/
def tateNormSubgroup (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A :=
  MonoidHom.range (tateNormHom (G := G) (A := A))

/-- Herbrand-quotient theory: the norm kernel `{a | N_G a = 1}`. -/
def normKernelSubgroup (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Subgroup A :=
  MonoidHom.ker (tateNormHom (G := G) (A := A))

/-- Herbrand-quotient theory: the augmentation image `I_G A` for a chosen `σ`. -/
def augmentationSubgroup (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) : Subgroup A :=
  MonoidHom.range (sigmaMinusOneHom (G := G) (A := A) σ)

/-- Herbrand-quotient theory: multiplicative model of `H⁰(G,A)=A^G/N_G A`. -/
def HerbrandH0 (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : Type uA :=
  fixedSubgroup G A ⧸ (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)

/-- Herbrand-quotient theory: multiplicative model of
`H^{-1}(G,A) = ker(N_G)/I_G A` for a chosen generator `σ`. -/
def HerbrandHMinusOne (G : Type uG) (A : Type uA) [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) : Type uA :=
  normKernelSubgroup G A ⧸ (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)

/-- Degree-zero Herbrand cohomology is a commutative group. -/
instance herbrandH0CommGroup {G : Type uG} {A : Type uA} [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A] : CommGroup (HerbrandH0 G A) := by
  unfold HerbrandH0
  infer_instance

/-- Degree-minus-one Herbrand cohomology is a commutative group. -/
instance herbrandHMinusOneCommGroup {G : Type uG} {A : Type uA} [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A] (σ : G) :
    CommGroup (HerbrandHMinusOne G A σ) := by
  unfold HerbrandHMinusOne
  infer_instance

/-- The sole public equivalence to the concrete quotient implementing
`H⁰(G,A)`. -/
def HerbrandH0.equiv {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] :
    HerbrandH0 G A ≃*
      fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A) := by
  change
    (fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)) ≃*
      fixedSubgroup G A ⧸
        (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A)
  exact MulEquiv.refl _

/-- The sole public equivalence to the concrete quotient implementing
`H⁻¹(G,A)`. -/
def HerbrandHMinusOne.equiv {G : Type uG} {A : Type uA} [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A] (σ : G) :
    HerbrandHMinusOne G A σ ≃*
      normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A) := by
  change
    (normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)) ≃*
      normKernelSubgroup G A ⧸
        (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A)
  exact MulEquiv.refl _

/-- Canonical projection from fixed points to `H⁰(G,A)`. -/
def HerbrandH0.mk {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] : fixedSubgroup G A →* HerbrandH0 G A := by
  unfold HerbrandH0
  exact QuotientGroup.mk'
    ((tateNormSubgroup G A).subgroupOf (fixedSubgroup G A))

/-- Canonical projection from the norm kernel to `H⁻¹(G,A)`. -/
def HerbrandHMinusOne.mk {G : Type uG} {A : Type uA} [Group G] [Fintype G]
    [CommGroup A] [MulDistribMulAction G A] (σ : G) :
    normKernelSubgroup G A →* HerbrandHMinusOne G A σ := by
  unfold HerbrandHMinusOne
  exact QuotientGroup.mk'
    ((augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A))

/-- Degree-zero Herbrand cohomology is finite when the coefficient group is finite. -/
noncomputable instance herbrandH0FiniteOfFinite {G : Type uG} {A : Type uA} [Group G]
    [Fintype G] [CommGroup A] [MulDistribMulAction G A] [Finite A] :
    Finite (HerbrandH0 G A) := by
  exact Finite.of_equiv
    (fixedSubgroup G A ⧸
      (tateNormSubgroup G A).subgroupOf (fixedSubgroup G A))
    (HerbrandH0.equiv (G := G) (A := A)).symm.toEquiv

/-- Degree-minus-one Herbrand cohomology is finite when the coefficient group is finite. -/
noncomputable instance herbrandHMinusOneFiniteOfFinite {G : Type uG} {A : Type uA}
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A] (σ : G) [Finite A] :
    Finite (HerbrandHMinusOne G A σ) := by
  exact Finite.of_equiv
    (normKernelSubgroup G A ⧸
      (augmentationSubgroup G A σ).subgroupOf (normKernelSubgroup G A))
    (HerbrandHMinusOne.equiv (G := G) (A := A) σ).symm.toEquiv

/-- Norm image subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionTateNormSubgroup {G : Type uG} {B : Type uB} [Group G]
    [Fintype G] [CommGroup B] : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact tateNormSubgroup G (G → B)

/-- `H⁰` of the right-regular multiplicative induced module. -/
def rightRegularFunctionHerbrandH0 {G : Type uG} {B : Type uB} [Group G] [Fintype G]
    [CommGroup B] := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact HerbrandH0 G (G → B)

/-- Degree-zero Herbrand cohomology of right-regular functions is a commutative group. -/
noncomputable instance rightRegularFunctionHerbrandH0CommGroup {G : Type uG} {B : Type uB}
    [Group G] [Fintype G] [CommGroup B] :
    CommGroup (rightRegularFunctionHerbrandH0 (G := G) (B := B)) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  change CommGroup (HerbrandH0 G (G → B))
  infer_instance

/-- Norm-kernel subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionNormKernelSubgroup {G : Type uG} {B : Type uB} [Group G]
    [Fintype G] [CommGroup B] : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact normKernelSubgroup G (G → B)

/-- Augmentation subgroup of the right-regular multiplicative induced module. -/
abbrev rightRegularFunctionAugmentationSubgroup {G : Type uG} {B : Type uB} [Group G]
    [CommGroup B] (σ : G) : Subgroup (G → B) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact augmentationSubgroup G (G → B) σ

/-- `H^{-1}` of the right-regular multiplicative induced module. -/
def rightRegularFunctionHerbrandHMinusOne {G : Type uG} {B : Type uB} [Group G]
    [Fintype G] [CommGroup B] (σ : G) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  exact HerbrandHMinusOne G (G → B) σ

/-- Degree-minus-one Herbrand cohomology of right-regular functions is a commutative group. -/
noncomputable instance rightRegularFunctionHerbrandHMinusOneCommGroup {G : Type uG}
    {B : Type uB} [Group G] [Fintype G] [CommGroup B] (σ : G) :
    CommGroup
      (rightRegularFunctionHerbrandHMinusOne (G := G) (B := B) σ) := by
  letI := rightRegularFunctionMulDistribMulAction (G := G) (B := B)
  change CommGroup (HerbrandHMinusOne G (G → B) σ)
  infer_instance

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
