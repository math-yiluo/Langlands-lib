/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeHomNormalization
import WeilConjectures.AlgebraicGeometry.EtaleAffineSingletonTensorDegreeInverseBijective

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Every normalized affine degree comparison has a two-sided inverse.
Source: Stacks Project, Tag 03P2, affine calculation; Tags 01I9 and 01IA.
(blueprint: new-etale-affine-singleton-tensor-degree-comparison-inverse)

Compare tensor pullback with Mathlib pullback by uniqueness of the left
adjoint to the same pushforward, respecting their units. This transports
quasi-coherence of U*F from the Mathlib pullback theorem.

Proof: apply the affine pullback sections formula to P → U and U*F;
quasi-coherence of U*F follows from that of F. The affine ring comparison
and the unit-normalized composition isomorphism turn it into a bijective
additive comparison c. Lift it and invert singleton product evaluation.
Its pure-tensor formula agrees with the assumed formula of f. To prove
f = c, evaluate at the unique product index and use ordinary tensor
induction followed by indexed tensor induction. Scalar multiples of pure
indexed tensors move to the coefficient factor by the balanced relation,
so the assumed equations determine the maps on additive generators.
Thus f is bijective; its inverse additive homomorphism gives inv. The two
inverse equations hold on elements and hence as categorical morphisms.
For n=0 this is the affine sections formula; for empty W both groups vanish.
-/
theorem exists_singletonTensorDegreeComparison_inverse
    (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U W : X.Etale) (g : W ⟶ U) (hU : IsAffine U.left) (hW : IsAffine W.left)
    (n : ℕ)
    (f : (singletonTensorAmitsur X F U W g).X n ⟶
      (singletonTensorCech X F U W g).X n)
    (hf : IsSingletonTensorDegreeComparisonHom X F U W g n f) :
    ∃ inv : (singletonTensorCech X F U W g).X n ⟶
      (singletonTensorAmitsur X F U W g).X n,
      f ≫ inv = 𝟙 _ ∧ inv ≫ f = 𝟙 _ := by
  have hb := singletonTensorDegreeComparisonHom_bijective X F U W g hU hW n f hf
  let e : (singletonTensorAmitsur X F U W g).X n ≃+
      (singletonTensorCech X F U W g).X n :=
    AddEquiv.ofBijective (AddCommGrpCat.Hom.hom f) hb
  let inv : (singletonTensorCech X F U W g).X n ⟶
      (singletonTensorAmitsur X F U W g).X n :=
    AddCommGrpCat.ofHom e.symm.toAddMonoidHom
  refine ⟨inv, ?_, ?_⟩
  · apply AddCommGrpCat.hom_ext
    ext x
    change e.symm (e x) = x
    simp
  · apply AddCommGrpCat.hom_ext
    ext x
    change e (e.symm x) = x
    simp

end
end AlgebraicGeometry.Scheme
