/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerKernel

/-! # Inclusion of consecutive nilpotent-units kernels

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Consecutive ideal powers decrease, checked on every affine open.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion) -/
theorem reduction_nilradical_power_le (X : Scheme.{u}) (j : ℕ) :
    X.nilradical ^ (j + 1 + 1) ≤ X.nilradical ^ (j + 1) := by
  rw [pow_succ]
  intro U
  exact Ideal.mul_le_left

/-- Units trivial on the thicker closed subscheme are trivial on the thinner one.
Proof: the inclusion of the closed subschemes induces a map of their base changes
over each étale object. Its composite with the first projection is the first
projection. Functoriality of global sections and of the units functor therefore
transports the thicker kernel's zero equation to the thinner restriction map.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion) -/
theorem reductionUnitsPowerKernel_ι_comp (X : Scheme.{u}) (j : ℕ) :
    kernel.ι (gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1 + 1)).subschemeι) ≫
      gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1)).subschemeι = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  let i := IdealSheafData.inclusion (reduction_nilradical_power_le X j)
  let k := pullback.map U.unop.hom (X.nilradical ^ (j + 1)).subschemeι
    U.unop.hom (X.nilradical ^ (j + 1 + 1)).subschemeι
    (𝟙 U.unop.left) i (𝟙 X) (by simp) (by
      exact (Category.comp_id _).trans
        (IdealSheafData.inclusion_subschemeι (reduction_nilradical_power_le X j)).symm)
  have hk : k ≫ pullback.fst U.unop.hom
      (X.nilradical ^ (j + 1 + 1)).subschemeι =
      pullback.fst U.unop.hom (X.nilradical ^ (j + 1)).subschemeι := by
    dsimp only [k]
    simp only [pullback.map, pullback.lift_fst]
    exact Category.comp_id _
  have hz := congrArg (fun f => f.hom.app U)
    (kernel.condition
      (gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1 + 1)).subschemeι))
  change (kernel.ι (gmSheafToLowerStarGmSheaf
    (X.nilradical ^ (j + 1 + 1)).subschemeι)).hom.app U ≫
    CommRingCat.unitsAddCommGrpULift.map
      (Scheme.Γ.map (pullback.fst U.unop.hom
        (X.nilradical ^ (j + 1)).subschemeι).op) = 0
  change (kernel.ι (gmSheafToLowerStarGmSheaf
    (X.nilradical ^ (j + 1 + 1)).subschemeι)).hom.app U ≫
    CommRingCat.unitsAddCommGrpULift.map
      (Scheme.Γ.map (pullback.fst U.unop.hom
        (X.nilradical ^ (j + 1 + 1)).subschemeι).op) = 0 at hz
  rw [← hk, op_comp, Functor.map_comp, Functor.map_comp, ← Category.assoc, hz]
  exact zero_comp

/-- The inclusion `1+N^(j+2) → 1+N^(j+1)`, obtained by factoring the kernel
inclusion into Gm through the preceding kernel.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion) -/
noncomputable def reductionUnitsPowerInclusion (X : Scheme.{u}) (j : ℕ) :
    X.reductionUnitsPowerKernel (j + 1) ⟶ X.reductionUnitsPowerKernel j :=
  kernel.lift _ (kernel.ι _) (reductionUnitsPowerKernel_ι_comp X j)

/-- The kernel lift defining the inclusion commutes with the inclusions into Gm.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion) -/
@[reassoc (attr := simp)]
theorem reductionUnitsPowerInclusion_ι (X : Scheme.{u}) (j : ℕ) :
    X.reductionUnitsPowerInclusion j ≫
      kernel.ι (gmSheafToLowerStarGmSheaf (X.nilradical ^ (j + 1)).subschemeι) =
      kernel.ι (gmSheafToLowerStarGmSheaf
        (X.nilradical ^ (j + 1 + 1)).subschemeι) :=
  kernel.lift_ι _ _ _

/-- The constructed inclusion is monic: its composite with a kernel inclusion
is a kernel inclusion and hence monic.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-power-inclusion) -/
instance mono_reductionUnitsPowerInclusion (X : Scheme.{u}) (j : ℕ) :
    Mono (X.reductionUnitsPowerInclusion j) :=
  mono_of_mono_fac (X.reductionUnitsPowerInclusion_ι j)

end AlgebraicGeometry.Scheme
