import Langlands.GroupScheme.GeometricComponents
import Langlands.GroupScheme.ComponentFieldEmbeddings

/-! # Comparing chosen geometric components along a specified closure embedding -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra (AlgebraicClosure k) L] [IsScalarTower k (AlgebraicClosure k) L]
  [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Compare the chosen geometric component group with the full component group
over L, using the specified compatible embedding of the chosen closure into L. -/
def geometricComponentEmbeddingEquiv :
    GeometricComponents k H ≃* AlgebraicallyClosedComponents (baseChanged k L H) :=
  componentFieldEmbeddingEquiv k (AlgebraicClosure k) L H

/-- The comparison preserves the actual component quotient topologies. -/
def geometricComponentEmbeddingHomeomorph :
    GeometricComponents k H ≃ₜ AlgebraicallyClosedComponents (baseChanged k L H) where
  toEquiv := (geometricComponentEmbeddingEquiv k L H).toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp]
theorem geometricComponentEmbeddingHomeomorph_apply (c : GeometricComponents k H) :
    geometricComponentEmbeddingHomeomorph k L H c =
      geometricComponentEmbeddingEquiv k L H c :=
  rfl

/-- The chosen comparison sends a section's component to that of its actual
extension through the specified coefficient embedding and pullback tower. -/
@[simp]
theorem geometricComponentEmbeddingEquiv_ofPoint
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentEmbeddingEquiv k L H (geometricComponentOfPoint k H x) =
      allComponentOfPoint _ (fieldEmbeddingSectionHom k (AlgebraicClosure k) L H x) :=
  componentFieldEmbeddingEquiv_ofPoint k (AlgebraicClosure k) L H x

/-- Compatible coefficient automorphisms intertwine the chosen absolute
Galois action and the coefficient action on all components over L. -/
theorem geometricComponentEmbeddingEquiv_smul
    (σ : Field.absoluteGaloisGroup k) (τ : L ≃ₐ[k] L)
    (h : ∀ a : AlgebraicClosure k,
      τ (algebraMap (AlgebraicClosure k) L a) =
        algebraMap (AlgebraicClosure k) L
          (AlgEquiv.toAlgHom σ a))
    (c : GeometricComponents k H) :
    geometricComponentEmbeddingEquiv k L H (σ • c) =
      allComponentConjugate k L H τ (geometricComponentEmbeddingEquiv k L H c) := by
  change componentFieldEmbeddingEquiv k (AlgebraicClosure k) L H
      (allComponentConjugate k (AlgebraicClosure k) H σ c) =
    allComponentConjugate k L H τ
      (componentFieldEmbeddingEquiv k (AlgebraicClosure k) L H c)
  exact componentFieldEmbeddingEquiv_conjugate k (AlgebraicClosure k) L H σ τ h c

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Chosen geometric-component comparisons are natural in actual homomorphisms
over the original field. -/
theorem geometricComponentEmbeddingEquiv_naturality (f : H ⟶ H')
    (c : GeometricComponents k H) :
    geometricComponentEmbeddingEquiv k L H' (geometricComponentMap k f c) =
      allComponentMap ((GroupScheme.baseChange (baseMap k L)).map f)
        (geometricComponentEmbeddingEquiv k L H c) :=
  componentFieldEmbeddingEquiv_naturality k (AlgebraicClosure k) L f c

end Langlands.GroupScheme.IdentityComponent
