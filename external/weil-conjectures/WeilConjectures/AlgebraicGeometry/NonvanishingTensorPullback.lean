/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Nonvanishing of a section after tensor pullback -/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of a section of an invertible module has nonzero residue-field value exactly
above its original nonvanishing locus.

Source: Stacks Project, Sheaves Tag 0098 and Properties Section 01PR.
(blueprint: lem-sc-nonvanishing-tensor-pullback).

Proof: the tensor-pullback stalk is the original stalk extended along the local ring
map, and the canonical unit sends the germ to one tensor the original germ. Passing to
the residue field identifies the resulting fibre with extension of the original fibre
along the residue-field homomorphism. The kernel of the map to the fibre is the maximal
ideal times the stalk module. Extension of a vector space along a field embedding is
faithful: after choosing a basis, one tensor a vector is zero exactly when that vector
is zero. Consequently the germ of the pulled-back section lies in the target maximal
ideal times its module exactly when the original germ lies in the source maximal ideal
times its module. Negating this equivalence is the stated criterion. No finiteness of
the scheme is required; the empty scheme satisfies the same criterion. -/
theorem nonvanishing_tensorPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) [N.IsInvertible]
    (t : Γ(N, ⊤)) (x : X) :
    let adj := Classical.choose (exists_tensorPullbackAdjunction f)
    let res : Γ((tensorPullback f).obj N, ⊤) := (adj.unit.app N).val.app (op ⊤) t
    x ∈ nonvanishingLocus ((tensorPullback f).obj N) res ↔
      f x ∈ nonvanishingLocus N t  := by
  classical
  dsimp only
  have hvalue {Z : Scheme.{u}} (P : Z.Modules) (z : Z) (s : Γ(P, ⊤)) :
      residueValue s z trivial = 0 ↔
        (TopCat.Presheaf.germ P.val.presheaf ⊤ z trivial) s ∈
          (IsLocalRing.maximalIdeal (Z.presheaf.stalk z)) •
            (⊤ : Submodule (Z.presheaf.stalk z) ↑(TopCat.Presheaf.stalk P.val.presheaf z)) := by
    change (1 : IsLocalRing.ResidueField (Z.presheaf.stalk z)) ⊗ₜ[Z.presheaf.stalk z]
      P.presheaf.germ ⊤ z trivial s = 0 ↔ _
    rw [← (TensorProduct.quotTensorEquivQuotSMul
      ↑(P.presheaf.stalk z) (IsLocalRing.maximalIdeal (Z.presheaf.stalk z))).map_eq_zero_iff]
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
    rfl
  obtain ⟨e, he⟩ := (invertible_pullback_tensor f).2.2.2.2.2.2.1 N x
  let := (f.residueFieldMap x).hom.toAlgebra
  have hinj : Function.Injective e.hom := (ModuleCat.mono_iff_injective e.hom).mp
    inferInstance
  have hz : residueValue
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app N).val.app (op ⊤) t)
        x trivial = 0 ↔ residueValue t (f x) trivial = 0 := by
    rw [← (map_eq_zero_iff e.hom.hom hinj), he ⊤ trivial t]
    exact Module.FaithfullyFlat.one_tmul_eq_zero_iff (Y.residueField (f x))
      (residueFiber N (f x)) _
  change ¬ _ ↔ ¬ _
  exact not_congr ((hvalue _ _ _).symm.trans (hz.trans (hvalue _ _ _)))


end AlgebraicGeometry.Scheme.Modules
