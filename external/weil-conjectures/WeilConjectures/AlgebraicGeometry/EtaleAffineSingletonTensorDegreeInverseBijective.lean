/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeKernel
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeSurjective

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- A normalized affine singleton tensor comparison homomorphism is bijective.
Source: Stacks Project, Tag 03P2, affine tensor calculation.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-bijective)
The affine sections and tensor-generator argument identifies the homomorphism on
all additive generators with the canonical affine comparison, which is bijective.
-/
theorem singletonTensorDegreeComparisonHom_bijective
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    Function.Bijective (AddCommGrpCat.Hom.hom f) := by
  have hk := singletonTensorDegreeComparisonHom_kernel X F U W g hU hW n f hf
  have hs := singletonTensorDegreeComparisonHom_surjective X F U W g hU hW n f hf
  refine ⟨?_, hs⟩
  intro x y hxy
  have hzero : (AddCommGrpCat.Hom.hom f) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hk (x - y) hzero)

end
end AlgebraicGeometry.Scheme
