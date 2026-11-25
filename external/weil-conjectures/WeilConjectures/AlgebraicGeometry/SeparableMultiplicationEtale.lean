/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.RingHom.Smooth

/-!
# The multiplication of a finite separable field extension is étale

For a finite separable field extension `k'/k`, the multiplication map
`μ : k' ⊗[k] k' → k'` is étale: `Spec μ` is étale, being a section of the étale morphism
`Spec (k' ⊗[k] k') ⟶ Spec k'`. In particular `μ` is a smooth ring map.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- **The multiplication of a finite separable extension is étale.** For a finite separable
field extension `k'/k`, the morphism `Spec k' ⟶ Spec (k' ⊗[k] k')` induced by the multiplication
`μ : k' ⊗[k] k' → k'` is étale; in particular `μ` is a smooth ring map.

(blueprint: `lem-weil-pbc-finite-separable-multiplication-etale`) -/
theorem finite_separable_multiplication_etale (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [Algebra.IsSeparable k k'] :
    Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k').toRingHom)) ∧
    (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k').toRingHom.Smooth := by
  have : Algebra.FormallyEtale k k' := Algebra.FormallyEtale.of_isSeparable k k'
  have : Algebra.FinitePresentation k k' :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.Etale k k' := ⟨inferInstance, inferInstance⟩
  let g := Spec.map (CommRingCat.ofHom (algebraMap k' (k' ⊗[k] k')))
  have : Etale g := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  let f := Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k').toRingHom)
  have hfg : f ≫ g = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    simp
  have : Etale (f ≫ g) := by rw [hfg]; infer_instance
  have hf : Etale f := Etale.of_comp f g
  refine ⟨hf, ?_⟩
  have h := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hf
  let := (Algebra.TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k').toRingHom.toAlgebra
  have : Algebra.Etale (k' ⊗[k] k') k' := h
  exact (inferInstance : Algebra.Smooth (k' ⊗[k] k') k')

end AlgebraicGeometry
