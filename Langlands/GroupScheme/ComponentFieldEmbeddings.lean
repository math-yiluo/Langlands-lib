import Langlands.GroupScheme.AlgebraicallyClosedComponentEquivalences

/-! # Component comparisons along specified coefficient-field embeddings -/

noncomputable section

set_option maxHeartbeats 200000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local irreducible] Langlands.GroupScheme.GaloisPointComparison.towerBaseChangeIso

namespace Langlands.GroupScheme.GaloisPointComparison

open GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (H : GroupScheme (Spec (CommRingCat.of k)))

private theorem coefficient_section_extension
    (x : rationalPoints (baseChanged k L H)) :
    coefficientBaseChangeEquiv k L M H
        (baseChangeCoeffEquiv L M (baseChanged k L H)
          (baseChangeSectionHom (baseMap L M) (baseChanged k L H) x)) =
      relativeExtend k L M H (baseChangeCoeffEquiv k L H x) := by
  rw [← rationalExtend_eq_baseChangeSectionHom L M,
    baseChangeCoeffEquiv_rationalExtend, coefficientBaseChangeEquiv_extend,
    coefficientBaseChangeEquiv_rationalCoeffEquiv]

private structure EmbeddingSectionData where
  hom : rationalPoints (baseChanged k L H) →* rationalPoints (baseChanged k M H)
  coefficient_formula (x : rationalPoints (baseChanged k L H)) :
    baseChangeCoeffEquiv k M H (hom x) =
      relativeExtend k L M H (baseChangeCoeffEquiv k L H x)

-- Check the construction and its coefficient law before specializing the
-- isomorphism. Opacity avoids expanding the concrete tower isomorphism again.
private opaque buildEmbeddingSectionData
    (i : baseChanged L M (baseChanged k L H) ≅ baseChanged k M H)
    (hi : ∀ x : rationalPoints (baseChanged L M (baseChanged k L H)),
      baseChangeCoeffEquiv k M H (rationalPoints.map i.hom x) =
        coefficientBaseChangeEquiv k L M H
          (baseChangeCoeffEquiv L M (baseChanged k L H) x)) :
    EmbeddingSectionData k L M H := by
  refine ⟨(rationalPoints.map i.hom).comp
    (baseChangeSectionHom (baseMap L M) (baseChanged k L H)), ?_⟩
  intro x
  exact (hi _).trans (coefficient_section_extension k L M H x)

private def fieldEmbeddingSectionData : EmbeddingSectionData k L M H :=
  buildEmbeddingSectionData k L M H (towerBaseChangeIso k L M H)
    (baseChangeCoeffEquiv_towerBaseChangeIso k L M H)

/-- Extend an actual section along the specified L-to-M embedding and use the
actual tower isomorphism to return to the direct base change of H. -/
def fieldEmbeddingSectionHom :
    rationalPoints (baseChanged k L H) →* rationalPoints (baseChanged k M H) :=
  (fieldEmbeddingSectionData k L M H).hom

/-- The actual section map is extension on the original coefficient carrier. -/
theorem baseChangeCoeffEquiv_fieldEmbeddingSectionHom
    (x : rationalPoints (baseChanged k L H)) :
    baseChangeCoeffEquiv k M H (fieldEmbeddingSectionHom k L M H x) =
      relativeExtend k L M H (baseChangeCoeffEquiv k L H x) :=
  (fieldEmbeddingSectionData k L M H).coefficient_formula x

/-- Compatible coefficient automorphisms intertwine the actual section extension. -/
theorem fieldEmbeddingSectionHom_conjugate [IsAffine H.X.left]
    (σ : L ≃ₐ[k] L) (τ : M ≃ₐ[k] M)
    (h : ∀ a : L, τ (algebraMap L M a) = algebraMap L M (σ a))
    (x : rationalPoints (baseChanged k L H)) :
    fieldEmbeddingSectionHom k L M H (rationalConjugate k L H σ x) =
      rationalConjugate k M H τ (fieldEmbeddingSectionHom k L M H x) := by
  apply (baseChangeCoeffEquiv k M H).injective
  simp only [baseChangeCoeffEquiv_fieldEmbeddingSectionHom,
    baseChangeCoeffEquiv_rationalConjugate]
  apply (coordinates k H M).injective
  ext a
  simp only [coordinates_relativeExtend, coordinates_conjugate]
  exact (h _).symm

variable {H} {H' : GroupScheme (Spec (CommRingCat.of k))}

/-- Section extension is natural in an actual homomorphism over the original field. -/
theorem fieldEmbeddingSectionHom_naturality (f : H ⟶ H')
    (x : rationalPoints (baseChanged k L H)) :
    fieldEmbeddingSectionHom k L M H'
        (rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map f) x) =
      rationalPoints.map ((GroupScheme.baseChange (baseMap k M)).map f)
        (fieldEmbeddingSectionHom k L M H x) := by
  apply (baseChangeCoeffEquiv k M H').injective
  rw [baseChangeCoeffEquiv_fieldEmbeddingSectionHom,
    baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_map,
    baseChangeCoeffEquiv_fieldEmbeddingSectionHom]
  exact congrArg (fun m => m (baseChangeCoeffEquiv k L H x))
    (H.affinePointsTarget_naturality f
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M)))

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

section PointFormulas

variable {F : Type u} [Field F] [IsAlgClosed F]
  {G G' : GroupScheme (Spec (CommRingCat.of F))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [Smooth G'.X.hom] [IsAffineHom G'.X.hom]

/-- The actual component map sends a section's component to its image's component. -/
@[simp]
theorem allComponentMap_ofPoint (f : G ⟶ G') (x : rationalPoints G) :
    allComponentMap f (allComponentOfPoint G x) =
      allComponentOfPoint G' (rationalPoints.map f x) := by
  rw [allComponentMap_apply]
  rfl

end PointFormulas

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  [IsAlgClosed L] [IsAlgClosed M]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

private structure EmbeddingComponentData (s : EmbeddingSectionData k L M H) where
  equiv : AlgebraicallyClosedComponents (baseChanged k L H) ≃*
    AlgebraicallyClosedComponents (baseChanged k M H)
  point_formula (x : rationalPoints (baseChanged k L H)) :
    equiv (allComponentOfPoint _ x) = allComponentOfPoint _ (s.hom x)

-- This body constructs the equivalence and proves its section formula;
-- specialization uses the published actual tower comparison and its law.
private opaque buildEmbeddingComponentData
    (i : baseChanged L M (baseChanged k L H) ≅ baseChanged k M H)
    (hi : ∀ x : rationalPoints (baseChanged L M (baseChanged k L H)),
      baseChangeCoeffEquiv k M H (rationalPoints.map i.hom x) =
        coefficientBaseChangeEquiv k L M H
          (baseChangeCoeffEquiv L M (baseChanged k L H) x))
    (s : EmbeddingSectionData k L M H) : EmbeddingComponentData k L M H s := by
  refine ⟨(allComponentBaseChangeEquiv (baseChanged k L H) (algebraMap L M)).trans
    (allComponentIso i), ?_⟩
  intro x
  change allComponentMap i.hom
    (allComponentBaseChange (baseChanged k L H) (algebraMap L M)
      (allComponentOfPoint _ x)) = _
  rw [allComponentBaseChange_ofPoint, allComponentMap_ofPoint]
  apply congrArg (allComponentOfPoint (baseChanged k M H))
  apply (baseChangeCoeffEquiv k M H).injective
  exact (hi _).trans ((coefficient_section_extension k L M H x).trans
    (s.coefficient_formula x).symm)

private def fieldEmbeddingComponentData :
    EmbeddingComponentData k L M H (fieldEmbeddingSectionData k L M H) :=
  buildEmbeddingComponentData k L M H (towerBaseChangeIso k L M H)
    (baseChangeCoeffEquiv_towerBaseChangeIso k L M H) (fieldEmbeddingSectionData k L M H)

/-- The component equivalence along the specified coefficient embedding. -/
def componentFieldEmbeddingEquiv :
    AlgebraicallyClosedComponents (baseChanged k L H) ≃*
      AlgebraicallyClosedComponents (baseChanged k M H) :=
  (fieldEmbeddingComponentData k L M H).equiv

/-- The comparison sends an actual section to its actual extended section. -/
@[simp]
theorem componentFieldEmbeddingEquiv_ofPoint
    (x : rationalPoints (baseChanged k L H)) :
    componentFieldEmbeddingEquiv k L M H (allComponentOfPoint _ x) =
      allComponentOfPoint _ (fieldEmbeddingSectionHom k L M H x) :=
  (fieldEmbeddingComponentData k L M H).point_formula x

/-- On actual sections, the full component action is coefficient conjugation. -/
theorem allComponentConjugate_ofPoint (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L H)) :
    allComponentConjugate k L H σ (allComponentOfPoint _ x) =
      allComponentOfPoint _ (rationalConjugate k L H σ x) := by
  rw [allComponentConjugate_apply]
  exact coefficientComponents_pointComponent k L H σ x

/-- The comparison is equivariant for every pair of automorphisms commuting
with the specified field embedding. -/
theorem componentFieldEmbeddingEquiv_conjugate
    (σ : L ≃ₐ[k] L) (τ : M ≃ₐ[k] M)
    (h : ∀ a : L, τ (algebraMap L M a) = algebraMap L M (σ a))
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    componentFieldEmbeddingEquiv k L M H (allComponentConjugate k L H σ c) =
      allComponentConjugate k M H τ (componentFieldEmbeddingEquiv k L M H c) := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  obtain ⟨x, rfl⟩ := allComponentOfPoint_surjective (baseChanged k L H) c
  rw [allComponentConjugate_ofPoint k L H,
    componentFieldEmbeddingEquiv_ofPoint, componentFieldEmbeddingEquiv_ofPoint,
    allComponentConjugate_ofPoint k M H]
  rw [fieldEmbeddingSectionHom_conjugate k L M H σ τ h]

variable {H}
  {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Comparisons along a specified embedding commute with maps defined over k. -/
theorem componentFieldEmbeddingEquiv_naturality (f : H ⟶ H')
    (c : AlgebraicallyClosedComponents (baseChanged k L H)) :
    componentFieldEmbeddingEquiv k L M H'
        (allComponentMap ((GroupScheme.baseChange (baseMap k L)).map f) c) =
      allComponentMap ((GroupScheme.baseChange (baseMap k M)).map f)
        (componentFieldEmbeddingEquiv k L M H c) := by
  obtain ⟨x, rfl⟩ := allComponentOfPoint_surjective (baseChanged k L H) c
  rw [allComponentMap_ofPoint, componentFieldEmbeddingEquiv_ofPoint,
    componentFieldEmbeddingEquiv_ofPoint, allComponentMap_ofPoint,
    fieldEmbeddingSectionHom_naturality]

end Langlands.GroupScheme.IdentityComponent

namespace Langlands.GroupScheme.GaloisPoint

section Identity

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- Extending coefficients along the identity field embedding is the identity. -/
@[simp]
theorem relativeExtend_self :
    relativeExtend k L L H = MonoidHom.id (H.affinePoints (CommAlgCat.of k L)) := by
  have h : CommAlgCat.ofHom (IsScalarTower.toAlgHom k L L) =
      𝟙 (CommAlgCat.of k L) := by
    ext a
    rfl
  rw [relativeExtend, h, affinePointMap_id]

end Identity

section Tower

variable (k L M N : Type u) [Field k] [Field L] [Field M] [Field N]
  [Algebra k L] [Algebra k M] [Algebra k N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower k L M] [IsScalarTower k L N]
  [IsScalarTower k M N] [IsScalarTower L M N]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- Successive specified coefficient extensions equal the direct extension. -/
theorem relativeExtend_comp :
    (relativeExtend k M N H).comp (relativeExtend k L M H) =
      relativeExtend k L N H := by
  have h : CommAlgCat.ofHom (IsScalarTower.toAlgHom k L M) ≫
      CommAlgCat.ofHom (IsScalarTower.toAlgHom k M N) =
      CommAlgCat.ofHom (IsScalarTower.toAlgHom k L N) := by
    ext a
    exact (IsScalarTower.algebraMap_apply L M N a).symm
  rw [relativeExtend, relativeExtend, relativeExtend, ← affinePointMap_comp, h]

end Tower

end Langlands.GroupScheme.GaloisPoint

namespace Langlands.GroupScheme.GaloisPointComparison

open GaloisPoint

section Identity

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The actual section comparison for the identity embedding is the identity. -/
@[simp]
theorem fieldEmbeddingSectionHom_self :
    fieldEmbeddingSectionHom k L L H =
      MonoidHom.id (rationalPoints (baseChanged k L H)) := by
  apply MonoidHom.ext
  intro x
  apply (baseChangeCoeffEquiv k L H).injective
  rw [baseChangeCoeffEquiv_fieldEmbeddingSectionHom, relativeExtend_self]
  rfl

end Identity

section Tower

variable (k L M N : Type u) [Field k] [Field L] [Field M] [Field N]
  [Algebra k L] [Algebra k M] [Algebra k N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower k L M] [IsScalarTower k L N]
  [IsScalarTower k M N] [IsScalarTower L M N]
  (H : GroupScheme (Spec (CommRingCat.of k)))

/-- Actual section comparisons compose along a compatible field tower. -/
theorem fieldEmbeddingSectionHom_comp :
    (fieldEmbeddingSectionHom k M N H).comp (fieldEmbeddingSectionHom k L M H) =
      fieldEmbeddingSectionHom k L N H := by
  apply MonoidHom.ext
  intro x
  apply (baseChangeCoeffEquiv k N H).injective
  change baseChangeCoeffEquiv k N H
      (fieldEmbeddingSectionHom k M N H (fieldEmbeddingSectionHom k L M H x)) = _
  simp only [baseChangeCoeffEquiv_fieldEmbeddingSectionHom]
  exact congrArg (fun f => f (baseChangeCoeffEquiv k L H x))
    (relativeExtend_comp k L M N H)

end Tower

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

section Identity

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [IsAlgClosed L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The full component comparison for the identity embedding is the identity. -/
@[simp]
theorem componentFieldEmbeddingEquiv_self :
    componentFieldEmbeddingEquiv k L L H =
      MulEquiv.refl (AlgebraicallyClosedComponents (baseChanged k L H)) := by
  apply MulEquiv.ext
  intro c
  obtain ⟨x, rfl⟩ := allComponentOfPoint_surjective (baseChanged k L H) c
  rw [componentFieldEmbeddingEquiv_ofPoint, fieldEmbeddingSectionHom_self]
  rfl

end Identity

section Tower

variable (k L M N : Type u) [Field k] [Field L] [Field M] [Field N]
  [Algebra k L] [Algebra k M] [Algebra k N]
  [Algebra L M] [Algebra L N] [Algebra M N]
  [IsScalarTower k L M] [IsScalarTower k L N]
  [IsScalarTower k M N] [IsScalarTower L M N]
  [IsAlgClosed L] [IsAlgClosed M] [IsAlgClosed N]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- Full component comparisons compose along the specified compatible embeddings. -/
theorem componentFieldEmbeddingEquiv_trans :
    (componentFieldEmbeddingEquiv k L M H).trans
        (componentFieldEmbeddingEquiv k M N H) =
      componentFieldEmbeddingEquiv k L N H := by
  apply MulEquiv.ext
  intro c
  obtain ⟨x, rfl⟩ := allComponentOfPoint_surjective (baseChanged k L H) c
  simp only [MulEquiv.trans_apply, componentFieldEmbeddingEquiv_ofPoint]
  apply congrArg (allComponentOfPoint (baseChanged k N H))
  exact congrArg (fun f => f x) (fieldEmbeddingSectionHom_comp k L M N H)

end Tower

end Langlands.GroupScheme.IdentityComponent
