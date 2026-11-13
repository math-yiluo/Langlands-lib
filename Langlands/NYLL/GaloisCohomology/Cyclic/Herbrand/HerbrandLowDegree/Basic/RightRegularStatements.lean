/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.RightRegularDefinitions

/-!
# Low-degree Herbrand quotients: right-regular cyclic primitive targets

Modified by Worker 5086: extract the asserted types of M113.082–M113.084,
M113.086–M113.088, M113.090–M113.092 and M113.104 from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean` as closed
Prop-valued definitions. Prefix the source namespace with `Langlands.NYLL`,
append `Statement` to each theorem name, and quantify the complete elaborated
telescope (the section variables of source lines 62–64 that each theorem
includes after its `omit`, followed by its own binders) without changing
binder kinds or order. Reuse the adapted definitions of the sibling
`RightRegularDefinitions` module through the import above; omit all source
proof bodies. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

/-- Successor step for the cyclic partial primitive. -/
def rightRegularCyclicPartialProduct_succStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [CommGroup B]
    (σ : G) (f : G → B) (i : ℕ),
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f (i + 1) =
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f i * f (σ ^ i)

/-- The successor step is the desired coboundary equation away from the
wrap-around point. -/
def rightRegularCyclicPartialProduct_succ_mul_invStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [CommGroup B]
    (σ : G) (f : G → B) (i : ℕ),
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f (i + 1) *
        (rightRegularCyclicPartialProduct (G := G) (B := B) σ f i)⁻¹ =
      f (σ ^ i)

-- Preserve the source hypothesis names even when the conclusions do not mention them.
set_option linter.unusedVariables false in
/-- The product-one condition gives the wrap-around coboundary equation for
the cyclic partial primitive. -/
def rightRegularCyclicPartialProduct_wrap_mul_inv_of_eq_oneStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [CommGroup B]
    (σ : G) (f : G → B) {n : ℕ} (hn : 0 < n)
    (hprod : rightRegularCyclicPartialProduct (G := G) (B := B) σ f n = 1),
    rightRegularCyclicPartialProduct (G := G) (B := B) σ f 0 *
        (rightRegularCyclicPartialProduct (G := G) (B := B) σ f (n - 1))⁻¹ =
      f (σ ^ (n - 1))

/-- The cyclic index represents the original group element. -/
def rightRegularCyclicIndex_specStatement : Prop :=
  ∀ {G : Type uG} [Group G] [Fintype G]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (x : G),
    x = σ ^ (rightRegularCyclicIndex (G := G) σ hgen x).val

set_option linter.unusedVariables false in
/-- If a concrete `ZMod |G|` representative is known, the cyclic index chooser
returns it. -/
def rightRegularCyclicIndex_eq_of_reprStatement : Prop :=
  ∀ {G : Type uG} [Group G] [Fintype G]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {x : G} {m : ZMod (Fintype.card G)} (hm : x = σ ^ m.val),
    rightRegularCyclicIndex (G := G) σ hgen x = m

set_option linter.unusedVariables false in
/-- On natural powers in the standard range, the cyclic index has the expected
value. -/
def rightRegularCyclicIndex_val_pow_of_ltStatement : Prop :=
  ∀ {G : Type uG} [Group G] [Fintype G]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    {i : ℕ} (hi : i < Fintype.card G),
    (rightRegularCyclicIndex (G := G) σ hgen (σ ^ i)).val = i

set_option linter.unusedVariables false in
/-- Away from the wrap-around index, the cyclic primitive solves the
right-regular coboundary equation. -/
def rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_succ_ltStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) (x : G)
    (hix : (rightRegularCyclicIndex (G := G) σ hgen x).val + 1 < Fintype.card G),
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x

set_option linter.unusedVariables false in
/-- At the wrap-around index, the product-one condition makes the cyclic
primitive solve the right-regular coboundary equation. -/
def rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_index_eq_card_sub_oneStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B) (x : G)
    (hix : (rightRegularCyclicIndex (G := G) σ hgen x).val = Fintype.card G - 1)
    (hprod :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f (Fintype.card G) = 1),
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x

set_option linter.unusedVariables false in
/-- If the cyclic partial product over a full period is `1`, the group-indexed
cyclic primitive solves the right-regular coboundary equation at every point. -/
def rightRegularCyclicPrimitive_mul_sigma_mul_inv_of_partialProduct_eq_oneStatement : Prop :=
  ∀ {G : Type uG} {B : Type uB} [Group G] [Fintype G] [CommGroup B]
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) (f : G → B)
    (hprod :
      rightRegularCyclicPartialProduct (G := G) (B := B) σ f (Fintype.card G) = 1)
    (x : G),
    rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f (x * σ) *
        (rightRegularCyclicPrimitive (G := G) (B := B) σ hgen f x)⁻¹ =
      f x

set_option linter.unusedVariables false in
/-- Equivariance of `mulEquivRightRegularFunctionOfAddEquiv`, assuming the
input additive equivalence is right-regular equivariant pointwise. -/
def mulEquivRightRegularFunctionOfAddEquiv_commutesStatement : Prop :=
  ∀ {G : Type uG} [Group G]
    {M : Type uA} {D : Type uB}
    [AddCommGroup M] [DistribMulAction G M] [AddCommGroup D]
    (e : M ≃+ (G → D))
    (he : ∀ (g : G) (m : M) (x : G), e (g • m) x = e m (x * g))
    (g : G) (m : Multiplicative M) (x : G),
    letI := multiplicativeMulDistribMulActionOfDistribMulAction G M
    mulEquivRightRegularFunctionOfAddEquiv G e (g • m) x =
      mulEquivRightRegularFunctionOfAddEquiv G e m (x * g)

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
