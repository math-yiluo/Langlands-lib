/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Kernel of restriction on an additive ideal
(blueprint: lem-sc-etale-nested-ideal-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The additive kernel for J embeds in that for I and is the kernel of restriction to J.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-etale-nested-ideal-kernel)

Proof: The closed-subscheme inclusion Z_I to Z_J, base changed to each etale
object, factors the projection to X through the projection for J. Contravariance
of global functions therefore shows that the additive kernel for J vanishes on
restriction to I. Lift its kernel inclusion through the kernel for I to obtain k.
The lift equation gives compatibility of the two inclusions, and the kernel
condition for J gives the zero composite. For an arbitrary map g into the kernel
for I killed by restriction to J, compose g with its inclusion into additive
functions and lift uniquely through the kernel for J. Cancel the monomorphic
kernel inclusion for I to verify factorization through k, and cancel that for J
to verify uniqueness. This proves the limiting fork without affine covers or
gluing. For I=J the inclusion is the identity; for J=0 the vertex is zero, and
for empty objects all additive groups are zero. -/
theorem exists_etaleNestedIdealKernel (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    ∃ k : kernel (etaleAdditiveSheafToLowerStar J.subschemeι) ⟶
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      k ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) =
        kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι) ∧
      ∃ hz : k ≫ (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
          etaleAdditiveSheafToLowerStar J.subschemeι) = 0,
        Nonempty (IsLimit (KernelFork.ofι k hz)) := by
  have hv : kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι) ≫
      etaleAdditiveSheafToLowerStar I.subschemeι = 0 := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    let i := IdealSheafData.inclusion hJI
    let p := pullback.map U.unop.hom I.subschemeι U.unop.hom J.subschemeι
      (𝟙 U.unop.left) i (𝟙 X) (by simp) (by
        exact (Category.comp_id _).trans (IdealSheafData.inclusion_subschemeι hJI).symm)
    have hp : p ≫ pullback.fst U.unop.hom J.subschemeι =
        pullback.fst U.unop.hom I.subschemeι := by
      dsimp only [p]
      simp only [pullback.map, pullback.lift_fst]
      exact Category.comp_id _
    have hz := congrArg (fun f => f.hom.app U)
      (kernel.condition (etaleAdditiveSheafToLowerStar J.subschemeι))
    change (kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι)).hom.app U ≫
      etaleAdditiveCoefficients.map
        (Scheme.Γ.map (pullback.fst U.unop.hom I.subschemeι).op) = 0
    change (kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι)).hom.app U ≫
      etaleAdditiveCoefficients.map
        (Scheme.Γ.map (pullback.fst U.unop.hom J.subschemeι).op) = 0 at hz
    rw [← hp, op_comp, Functor.map_comp, Functor.map_comp, ← Category.assoc, hz]
    exact zero_comp
  let k := kernel.lift (etaleAdditiveSheafToLowerStar I.subschemeι)
    (kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι)) hv
  have hk : k ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) =
      kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι) := kernel.lift_ι _ _ _
  have hz : k ≫ (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
      etaleAdditiveSheafToLowerStar J.subschemeι) = 0 := by
    rw [← Category.assoc, hk, kernel.condition]
  refine ⟨k, hk, hz, ⟨KernelFork.IsLimit.ofι k hz
    (fun g hg => kernel.lift (etaleAdditiveSheafToLowerStar J.subschemeι)
      (g ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι))
      (by simpa only [Category.assoc] using hg)) ?_ ?_⟩⟩
  · intro W g hg
    apply (cancel_mono (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι))).mp
    simp only [Category.assoc, hk, kernel.lift_ι]
  · intro W g hg m hm
    apply (cancel_mono (kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι))).mp
    rw [kernel.lift_ι, ← hk, ← Category.assoc, hm]

end AlgebraicGeometry.Scheme
