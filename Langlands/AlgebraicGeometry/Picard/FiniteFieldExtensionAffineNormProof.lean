import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionAffineNormStatement
import Langlands.AlgebraicGeometry.Picard.FiniteFieldExtensionNormProof

/-! # Compatible norms on affine opens along a finite field-extension base change (proof) -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open FiniteFieldExtensionNorm in
/-- The affine norms `normAff` of the published all-open norm proof, restricted to the affine
opens of `X`, satisfy the three clauses of the affine statement. -/
theorem finiteFieldExtensionAffineNorm : FiniteFieldExtensionAffineNormStatement.{u} := by
  intro K L _ _ _ _ X p
  refine ⟨fun U => normAff L p (U : X.Opens), fun U V hUV f => normAff_res L p V.2 U.2 hUV f,
    fun U g => normAff_app L p U.2 g, fun U f => Set.ext fun x => ⟨fun h => ?_, ?_⟩⟩
  · have hx : x ∈ (U : X.Opens) := X.basicOpen_le _ h
    exact ⟨hx, (mem_basicOpen_normAff L p U.2 f x hx).mp h⟩
  · rintro ⟨hx, h⟩
    exact (mem_basicOpen_normAff L p U.2 f x hx).mpr h

end Langlands.AlgebraicGeometry.Picard
