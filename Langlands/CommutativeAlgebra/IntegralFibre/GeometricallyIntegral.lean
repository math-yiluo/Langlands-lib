import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Geometrically integral fibres in algebraic terms

If `Spec S → Spec R` is geometrically integral, then `K ⊗[R] S` is a domain for every field `K`
over `R`. -/

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Langlands.CommutativeAlgebra

/-- If `Spec S → Spec R` is geometrically integral, then `K ⊗[R] S` is a domain for every field
`K` with an `R`-algebra structure. -/
theorem isDomain_tensor_of_geometricallyIntegral {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (h : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (K : Type u) [Field K] [Algebra R K] : IsDomain (K ⊗[R] S) := by
  have h₁ : IsIntegral (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    pullback_of_geometrically h.geometrically_isIntegral K _
  have h₂ : IsIntegral (Spec (.of (S ⊗[R] K))) := IsIntegral.of_isIso (pullbackSpecIso R S K).hom
  have : IsDomain (S ⊗[R] K) := (affine_isIntegral_iff (.of (S ⊗[R] K))).mp h₂
  exact (Algebra.TensorProduct.comm R K S).toMulEquiv.isDomain (S ⊗[R] K)

end Langlands.CommutativeAlgebra
