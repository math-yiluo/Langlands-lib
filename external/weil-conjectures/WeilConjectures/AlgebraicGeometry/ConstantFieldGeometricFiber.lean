/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.RingTheory.ConstantField

/-!
# Connected geometric fibres over the constant field

An affine scheme `Spec A` over a field `k'` such that `A ⊗[k'] k̄'` is a domain has an irreducible,
hence connected, geometric fibre. By `Algebra.TensorProduct.isDomain_constantField` this applies
to an integrally closed domain `A` of finite type over a finite field `k₀`, over its constant field
`k'` (`AlgebraicGeometry.connectedSpace_geometricFiber_constantField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct

namespace AlgebraicGeometry

/-- If `A ⊗[k'] k̄'` is a domain, the geometric fibre of `Spec A ⟶ Spec k'` is irreducible. -/
theorem irreducibleSpace_geometricFiber_of_isDomain {k' A : Type u} [Field k'] [CommRing A]
    [Algebra k' A] [IsDomain (A ⊗[k'] AlgebraicClosure k')] :
    IrreducibleSpace (Spec.map (CommRingCat.ofHom (algebraMap k' A))).geometricFiber := by
  let e : (Spec.map (CommRingCat.ofHom (algebraMap k' A))).geometricFiber ≅
      Spec (.of (A ⊗[k'] AlgebraicClosure k')) := pullbackSpecIso k' A (AlgebraicClosure k')
  exact (Scheme.homeoOfIso e).symm.surjective.irreducibleSpace
    (Scheme.homeoOfIso e).symm.continuous

/-- **Geometric connectedness over the constant field.** For an integrally closed domain `A` of
finite type over a field `k₀`, `Spec A` is geometrically irreducible over its constant field `k'`
(the integral closure of `k₀` in `A`). -/
theorem irreducibleSpace_geometricFiber_constantField {k₀ : Type u} [Field k₀] {A : Type u}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra k₀ A] [PerfectField
      (Algebra.TensorProduct.ConstantField k₀ A)] :
    IrreducibleSpace (Spec.map (CommRingCat.ofHom (algebraMap
      (Algebra.TensorProduct.ConstantField k₀ A) A))).geometricFiber :=
  have := Algebra.TensorProduct.isDomain_constantField (k := k₀) (A := A)
    (AlgebraicClosure (Algebra.TensorProduct.ConstantField k₀ A))
  irreducibleSpace_geometricFiber_of_isDomain

end AlgebraicGeometry
