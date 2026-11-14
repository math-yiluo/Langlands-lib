/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

/-!
# Low-degree Herbrand quotients: evaluation, cardinality and vanishing targets

Modified by Worker 9: extract the asserted types of M113.014, M113.019,
M113.024–M113.027, M113.036–M113.041, M113.046, M113.047, M113.067, M113.069,
M113.070, M113.072, M113.075–M113.078 and M113.107–M113.109 from the pinned
NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` as
closed Prop-valued definitions. Prefix the source namespace with
`Langlands.NYLL`, append `Statement` to each theorem name, and quantify the
complete elaborated telescope (the section variables of source lines 62–64
that each theorem includes, after its `omit` where it has one, followed by its
own binders) without changing binder kinds or order. Reuse the adapted
definitions of the sibling `Definitions` module through the import above; keep
the `protected` modifier of the two `inductionOn` theorems; omit all source
proof bodies and the `@[simp]` attributes. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- The Tate norm homomorphism evaluates to the Tate norm. -/
def tateNormHom_applyStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : A),
    tateNormHom (G := G) (A := A) a = tateNorm G A a

/-- The sigma-minus-one homomorphism evaluates to the sigma-minus-one operator. -/
def sigmaMinusOneHom_applyStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : A),
    sigmaMinusOneHom (G := G) (A := A) σ a = sigmaMinusOne G A σ a

-- Preserve the source hypothesis names even when the conclusions do not mention them.
set_option linter.unusedVariables false in
/-- If `σ` generates `G`, the kernel of `a ↦ a^(σ-1)` is the fixed subgroup. -/
def sigmaMinusOneHom_ker_eq_fixedSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ),
    MonoidHom.ker (sigmaMinusOneHom (G := G) (A := A) σ) = fixedSubgroup G A

/-- Finite-module source: the norm homomorphism factors the cardinality of
`A` into norm-kernel and norm-image cardinalities. -/
def card_eq_card_normKernelSubgroup_mul_card_tateNormSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] [Finite A],
    Nat.card A = Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A)

set_option linter.unusedVariables false in
/-- Finite-module source: for a cyclic generator `σ`, the coboundary
homomorphism factors the cardinality of `A` into fixed and augmentation
cardinalities. -/
def card_eq_card_fixedSubgroup_mul_card_augmentationSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A],
    Nat.card A = Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ)

set_option linter.unusedVariables false in
/-- Finite-module cardinality balance behind `h(G,A)=1`: for a finite cyclic
group action, the product `#A^G · #I_G A` equals `#ker N_G · #N_G A`. -/
def herbrand_finite_module_cardinality_balanceStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A],
    Nat.card (fixedSubgroup G A) * Nat.card (augmentationSubgroup G A σ) =
      Nat.card (normKernelSubgroup G A) * Nat.card (tateNormSubgroup G A)

/-- The degree-zero quotient equivalence sends the canonical class to the raw quotient class. -/
def HerbrandH0.equiv_mkStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : fixedSubgroup G A),
    HerbrandH0.equiv (G := G) (A := A) (HerbrandH0.mk a) =
      QuotientGroup.mk a

/-- The degree-minus-one quotient equivalence sends the canonical class to the
raw quotient class. -/
def HerbrandHMinusOne.equiv_mkStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G) (a : normKernelSubgroup G A),
    HerbrandHMinusOne.equiv (G := G) (A := A) σ
        (HerbrandHMinusOne.mk σ a) =
      QuotientGroup.mk a

/-- Every degree-zero Herbrand class has a fixed-point representative. -/
def HerbrandH0.mk_surjectiveStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A],
    Function.Surjective (HerbrandH0.mk (G := G) (A := A))

/-- Every degree-minus-one Herbrand class has a norm-kernel representative. -/
def HerbrandHMinusOne.mk_surjectiveStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G),
    Function.Surjective (HerbrandHMinusOne.mk (G := G) (A := A) σ)

/-- A fixed-point representative gives the trivial degree-zero class exactly
when it is a Tate norm. -/
def HerbrandH0.mk_eq_one_iffStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (a : fixedSubgroup G A),
    HerbrandH0.mk a = 1 ↔ (a : A) ∈ tateNormSubgroup G A

/-- A norm-kernel representative gives the trivial degree-minus-one class
exactly when it is an augmentation. -/
def HerbrandHMinusOne.mk_eq_one_iffStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G)
    (a : normKernelSubgroup G A),
    HerbrandHMinusOne.mk σ a = 1 ↔
      (a : A) ∈ augmentationSubgroup G A σ

set_option linter.unusedVariables false in
/-- Eliminate a degree-zero Herbrand class through an arbitrary fixed-point
representative and the canonical class map. -/
protected def HerbrandH0.inductionOnStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    {motive : HerbrandH0 G A → Prop} (q : HerbrandH0 G A)
    (h : ∀ a : fixedSubgroup G A, motive (HerbrandH0.mk a)), motive q

set_option linter.unusedVariables false in
/-- Eliminate a degree-minus-one Herbrand class through an arbitrary
norm-kernel representative and the canonical class map. -/
protected def HerbrandHMinusOne.inductionOnStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G)
    {motive : HerbrandHMinusOne G A σ → Prop}
    (q : HerbrandHMinusOne G A σ)
    (h : ∀ a : normKernelSubgroup G A,
      motive (HerbrandHMinusOne.mk σ a)), motive q

/-- The augmentation image lies in the norm kernel. -/
def augmentationSubgroup_le_normKernelSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] (σ : G),
    augmentationSubgroup G A σ ≤ normKernelSubgroup G A

/-- The norm image lies in the fixed subgroup, as in Herbrand-quotient theory. -/
def tateNormSubgroup_le_fixedSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A],
    tateNormSubgroup G A ≤ fixedSubgroup G A

set_option linter.unusedVariables false in
/-- A quotient-level criterion for vanishing of `H⁰`: if every fixed point is
a norm, then the low-degree Herbrand `H⁰` quotient is a subsingleton. -/
def herbrandH0_subsingleton_of_fixed_le_tateNormSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (h : fixedSubgroup G A ≤ tateNormSubgroup G A),
    Subsingleton (HerbrandH0 G A)

set_option linter.unusedVariables false in
/-- A quotient-level criterion for vanishing of `H^{-1}`: if every norm-kernel
element is an augmentation element, then the low-degree Herbrand `H^{-1}`
quotient is a subsingleton. -/
def herbrandHMinusOne_subsingleton_of_normKernel_le_augmentationSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (h : normKernelSubgroup G A ≤ augmentationSubgroup G A σ),
    Subsingleton (HerbrandHMinusOne G A σ)

set_option linter.unusedVariables false in
/-- Transport the `H⁰` vanishing source `A^G ≤ N_G A` across an equivariant
multiplicative equivalence. -/
def fixed_le_tateNormSubgroup_of_mulEquivStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (hB : fixedSubgroup G B ≤ tateNormSubgroup G B),
    fixedSubgroup G A ≤ tateNormSubgroup G A

set_option linter.unusedVariables false in
/-- Transport the `H^{-1}` vanishing source `ker N_G ≤ I_G A` across an
equivariant multiplicative equivalence. -/
def normKernel_le_augmentationSubgroup_of_mulEquivStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ),
    normKernelSubgroup G A ≤ augmentationSubgroup G A σ

set_option linter.unusedVariables false in
/-- Transport low-degree `H⁰` triviality across an equivariant multiplicative
equivalence. -/
def herbrandH0_subsingleton_of_mulEquivStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (hB : fixedSubgroup G B ≤ tateNormSubgroup G B),
    Subsingleton (HerbrandH0 G A)

set_option linter.unusedVariables false in
/-- Transport low-degree `H^{-1}` triviality across an equivariant
multiplicative equivalence. -/
def herbrandHMinusOne_subsingleton_of_mulEquivStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    (e : A ≃* B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a)
    (σ : G) (hB : normKernelSubgroup G B ≤ augmentationSubgroup G B σ),
    Subsingleton (HerbrandHMinusOne G A σ)

/-- Quotient-cardinality source for `H⁰(G,A)=A^G/N_G A`. -/
def card_fixedSubgroup_eq_card_herbrandH0_mul_card_tateNormSubgroupStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A] [Finite A],
    Nat.card (fixedSubgroup G A) =
      Nat.card (HerbrandH0 G A) * Nat.card (tateNormSubgroup G A)

/-- Quotient-cardinality source for
`H^{-1}(G,A)=ker(N_G)/I_G A`. -/
def card_normKernelSubgroup_eq_card_herbrandHMinusOne_mul_card_augmentationSubgroupStatement :
    Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) [Finite A],
    Nat.card (normKernelSubgroup G A) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (augmentationSubgroup G A σ)

set_option linter.unusedVariables false in
/-- The two low-degree Herbrand quotients of a finite cyclic module have equal
cardinality, the finite-module source for Herbrand-quotient multiplicativity. -/
def herbrand_finite_module_card_eqStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} [Group G] [Fintype G] [CommGroup A]
    [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A],
    Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
