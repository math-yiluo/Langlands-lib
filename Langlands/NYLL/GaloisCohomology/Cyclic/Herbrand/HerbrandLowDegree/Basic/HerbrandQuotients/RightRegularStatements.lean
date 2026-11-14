/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.RightRegularDefinitions

/-!
# Low-degree Herbrand quotients: right-regular norm-kernel, augmentation and vanishing targets

Modified by Worker 9: extract the asserted types of M113.079, M113.093–M113.095,
M113.097, M113.099, M113.100, M113.105 and M113.106 from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` as closed
Prop-valued definitions. Prefix the source namespace with `Langlands.NYLL`,
append `Statement` to each theorem name, and quantify the complete elaborated
telescope (the section variables of source lines 62–64 that each theorem
includes after its `omit`, followed by its own binders) without changing
binder kinds or order. Reuse the adapted definitions of the sibling
`HerbrandQuotients.Definitions` and `RightRegularDefinitions` modules through
the imports above; keep the `letI` of M113.105 and M113.106 in the asserted
type; omit all source proof bodies. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- Membership in the right-regular norm kernel is the single product
condition `∏ g, f g = 1`. -/
def rightRegularFunction_mem_normKernelSubgroup_iffStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (f : G → B),
    f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ↔
      (∏ g : G, f g) = 1

-- Preserve the source hypothesis names even when the conclusions do not mention them.
set_option linter.unusedVariables false in
/-- A right-regular norm-kernel element has product `1` along one full cyclic
enumeration by a generator. -/
def rightRegularFunction_prod_powers_eq_one_of_mem_normKernelStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {f : G → B}
    (hf : f ∈ rightRegularFunctionNormKernelSubgroup (G := G) (B := B)),
    (Finset.range (Nat.card G)).prod (fun i => f (σ ^ i)) = 1

/-- Membership in the right-regular augmentation subgroup is the pointwise
difference equation `b (x * σ) * (b x)⁻¹ = f x`. -/
def rightRegularFunction_mem_augmentationSubgroup_iffStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [CommGroup B]
    (σ : G) (f : G → B),
    f ∈ rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ ↔
      ∃ b : G → B, ∀ x : G, b (x * σ) * (b x)⁻¹ = f x

set_option linter.unusedVariables false in
/-- Concrete `H^{-1}` source for the right-regular multiplicative induced
module: every norm-kernel element is an augmentation element. -/
def rightRegularFunction_normKernel_le_augmentationSubgroupStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ),
    rightRegularFunctionNormKernelSubgroup (G := G) (B := B) ≤
      rightRegularFunctionAugmentationSubgroup (G := G) (B := B) σ

/-- Concrete `H⁰` source for induced modules: for the right-regular
multiplicative induced module `G → B`, every fixed point is a norm. -/
def rightRegularFunction_fixed_le_tateNormSubgroupStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B],
    rightRegularFunctionFixedSubgroup (G := G) (B := B) ≤
      rightRegularFunctionTateNormSubgroup (G := G) (B := B)

set_option linter.unusedVariables false in
/-- Transport `H⁰` vanishing from the right-regular trivial-subgroup model
along an explicit multiplicative equivalence. -/
def herbrandH0_subsingleton_of_equiv_rightRegularFunctionStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [MulDistribMulAction G A]
    (e : A ≃* (G → B))
    (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g)),
    Subsingleton (HerbrandH0 G A)

set_option linter.unusedVariables false in
/-- Transport `H^{-1}` vanishing from the right-regular trivial-subgroup model
along an explicit multiplicative equivalence. -/
def herbrandHMinusOne_subsingleton_of_equiv_rightRegularFunctionStatement : Prop :=
  ∀ {G : Type uG} {A : Type uA} {B : Type uB} [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [MulDistribMulAction G A]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (e : A ≃* (G → B))
    (he : ∀ (g : G) (a : A) (x : G), e (g • a) x = e a (x * g)),
    Subsingleton (HerbrandHMinusOne G A σ)

set_option linter.unusedVariables false in
/-- `H⁰` vanishing for a multiplicative wrapper transported from an additive
right-regular equivalence. -/
def herbrandH0_subsingleton_of_addEquiv_rightRegularFunctionStatement : Prop :=
  ∀ {G : Type uG} [Group G] [Fintype G]
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g)),
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    Subsingleton (HerbrandH0 G (Multiplicative M))

set_option linter.unusedVariables false in
/-- `H^{-1}` vanishing for a multiplicative wrapper transported from an
additive right-regular equivalence. -/
def herbrandHMinusOne_subsingleton_of_addEquiv_rightRegularFunctionStatement : Prop :=
  ∀ {G : Type uG} [Group G] [Fintype G]
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g)),
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    Subsingleton (HerbrandHMinusOne G (Multiplicative M) σ)

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
