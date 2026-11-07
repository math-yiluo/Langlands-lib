import Langlands.GroupScheme.GeometricComponentCanonicalBaseChange

/-! # Canonical fixed components in a field tower -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local irreducible] Langlands.GroupScheme.GaloisPointComparison.towerBaseChangeIso

namespace Langlands.GroupScheme.GaloisPointComparison

section CoefficientEmbedding

variable (k K M N : Type u) [Field k] [Field K] [Field M] [Field N]
  [Algebra k K] [Algebra k M] [Algebra k N] [Algebra K M] [Algebra K N]
  [IsScalarTower k K M] [IsScalarTower k K N]
  (H : GroupScheme (Spec (CommRingCat.of k)))

private theorem coefficientBaseChangeEquiv_embedding
    (j : M →ₐ[K] N) (x : (baseChanged k K H).affinePoints (CommAlgCat.of K M)) :
    coefficientBaseChangeEquiv k K N H
        ((baseChanged k K H).affinePointMap (CommAlgCat.ofHom j) x) =
      H.affinePointMap (CommAlgCat.ofHom (j.restrictScalars k))
        (coefficientBaseChangeEquiv k K M H x) := by
  apply Over.OverMorphism.ext
  simp only [coefficientBaseChangeEquiv_left, affinePointMap_apply, Over.comp_left]
  exact Category.assoc _ _ _

end CoefficientEmbedding

section CoefficientTower

variable (k K L M : Type u) [Field k] [Field K] [Field L] [Field M]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra k M] [Algebra K M] [Algebra L M]
  [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
  (H : GroupScheme (Spec (CommRingCat.of k)))

omit [IsScalarTower k K L] in
private theorem coefficientBaseChangeEquiv_tower_of_projection
    (f : baseChanged K L (baseChanged k K H) ⟶ baseChanged k L H)
    (hf : f.hom.hom.left ≫ CategoryTheory.Limits.pullback.fst H.X.hom (baseMap k L) =
      CategoryTheory.Limits.pullback.fst (baseChanged k K H).X.hom (baseMap K L) ≫
        CategoryTheory.Limits.pullback.fst H.X.hom (baseMap k K))
    (x : (baseChanged K L (baseChanged k K H)).affinePoints (CommAlgCat.of L M)) :
    coefficientBaseChangeEquiv k L M H
        ((baseChanged K L (baseChanged k K H)).affinePointsTarget
          f (CommAlgCat.of L M) x) =
      coefficientBaseChangeEquiv k K M H
        (coefficientBaseChangeEquiv K L M (baseChanged k K H) x) := by
  apply Over.OverMorphism.ext
  simp only [coefficientBaseChangeEquiv_left, affinePointsTarget_apply, Over.comp_left]
  rw [Category.assoc, hf, Category.assoc]

private theorem coefficientBaseChangeEquiv_tower
    (x : (baseChanged K L (baseChanged k K H)).affinePoints (CommAlgCat.of L M)) :
    coefficientBaseChangeEquiv k L M H
        ((baseChanged K L (baseChanged k K H)).affinePointsTarget
          (towerBaseChangeIso k K L H).hom (CommAlgCat.of L M) x) =
      coefficientBaseChangeEquiv k K M H
        (coefficientBaseChangeEquiv K L M (baseChanged k K H) x) :=
  coefficientBaseChangeEquiv_tower_of_projection k K L M H
    (towerBaseChangeIso k K L H).hom (towerBaseChangeIso_hom_fst k K L H) x

end CoefficientTower

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

section Isomorphism

variable (k : Type u) [Field k]
  {H H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom]
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- An actual group-scheme isomorphism induces an equivalence on all Galois-fixed
geometric components. -/
def geometricComponentFixedIso (e : H ≅ H') :
    geometricComponentFixedSubgroup k H ≃* geometricComponentFixedSubgroup k H' where
  toFun := geometricComponentFixedMap k e.hom
  invFun := geometricComponentFixedMap k e.inv
  left_inv c := by
    have h := congrArg (fun f => f c) (geometricComponentFixedMap_comp k e.hom e.inv)
    simpa only [e.hom_inv_id, geometricComponentFixedMap_id, MonoidHom.id_apply,
      MonoidHom.comp_apply] using h.symm
  right_inv c := by
    have h := congrArg (fun f => f c) (geometricComponentFixedMap_comp k e.inv e.hom)
    simpa only [e.inv_hom_id, geometricComponentFixedMap_id, MonoidHom.id_apply,
      MonoidHom.comp_apply] using h.symm
  map_mul' := map_mul (geometricComponentFixedMap k e.hom)

@[simp]
theorem geometricComponentFixedIso_apply (e : H ≅ H')
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedIso k e c = geometricComponentFixedMap k e.hom c := rfl

end Isomorphism

section SectionEmbedding

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

private def sectionAlong (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    rationalPoints (baseChanged k (AlgebraicClosure k) H) →*
      rationalPoints (baseChanged K (AlgebraicClosure K) (baseChanged k K H)) := by
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeSectionHom k K H

private theorem sectionAlong_coefficient
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    coefficientBaseChangeEquiv k K (AlgebraicClosure K) H
        (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H)
          (sectionAlong k K H i x)) =
      H.affinePointMap (CommAlgCat.ofHom i)
        (baseChangeCoeffEquiv k (AlgebraicClosure k) H x) := by
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeSectionHom_coefficient k K H x

private theorem equivAlong_ofPoint
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentBaseChangeEquivOfEmbedding k K H i
        (geometricComponentOfPoint k H x) =
      geometricComponentOfPoint K (baseChanged k K H) (sectionAlong k K H i x) := by
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeEquiv_ofPoint k K H x

end SectionEmbedding

section Tower

variable (k K L : Type u) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

private theorem sectionAlong_tower
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    rationalPoints.map
        ((GroupScheme.baseChange (baseMap L (AlgebraicClosure L))).map
          (towerBaseChangeIso k K L H).hom)
        (sectionAlong K L (baseChanged k K H) j (sectionAlong k K H i x)) =
      sectionAlong k L H ((j.restrictScalars k).comp i) x := by
  apply (baseChangeCoeffEquiv L (AlgebraicClosure L) (baseChanged k L H)).injective
  apply (coefficientBaseChangeEquiv k L (AlgebraicClosure L) H).injective
  rw [baseChangeCoeffEquiv_map, coefficientBaseChangeEquiv_tower,
    sectionAlong_coefficient, coefficientBaseChangeEquiv_embedding,
    sectionAlong_coefficient, sectionAlong_coefficient]
  change Lie.affineMap H (j.restrictScalars k)
      (Lie.affineMap H i (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)) =
    Lie.affineMap H ((j.restrictScalars k).comp i)
      (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)
  rw [Lie.affineMap_comp]

/-- Successive geometric comparisons along two closure embeddings agree with
the direct comparison along their composite after the actual tower map. -/
theorem geometricComponentBaseChangeEquivOfEmbedding_tower
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (c : GeometricComponents k H) :
    geometricComponentMap L (towerBaseChangeIso k K L H).hom
        (geometricComponentBaseChangeEquivOfEmbedding K L (baseChanged k K H) j
          (geometricComponentBaseChangeEquivOfEmbedding k K H i c)) =
      geometricComponentBaseChangeEquivOfEmbedding k L H ((j.restrictScalars k).comp i) c := by
  obtain ⟨x, rfl⟩ := geometricComponentOfPoint_surjective k H c
  rw [equivAlong_ofPoint, equivAlong_ofPoint, geometricComponentMap_ofPoint,
    equivAlong_ofPoint, sectionAlong_tower]

/-- The actual pullback-tower isomorphism identifies the full fixed component
groups of the iterated and direct base changes. -/
def geometricComponentFixedTowerIso :
    geometricComponentFixedSubgroup L (baseChanged K L (baseChanged k K H)) ≃*
      geometricComponentFixedSubgroup L (baseChanged k L H) :=
  geometricComponentFixedIso L (towerBaseChangeIso k K L H)

@[simp]
theorem geometricComponentFixedTowerIso_val
    (c : geometricComponentFixedSubgroup L (baseChanged K L (baseChanged k K H))) :
    (geometricComponentFixedTowerIso k K L H c).val =
      geometricComponentMap L (towerBaseChangeIso k K L H).hom c.val := rfl

/-- Canonical extension of every Galois-fixed component through a field tower
agrees with direct extension under the actual tower identification. -/
theorem geometricComponentCanonicalBaseChange_tower
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedTowerIso k K L H
        (geometricComponentCanonicalBaseChange K L (baseChanged k K H)
          (geometricComponentCanonicalBaseChange k K H c)) =
      geometricComponentCanonicalBaseChange k L H c := by
  let i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let j : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  apply Subtype.ext
  rw [geometricComponentFixedTowerIso_val,
    geometricComponentCanonicalBaseChange_val K L (baseChanged k K H) j,
    geometricComponentCanonicalBaseChange_val k K H i,
    geometricComponentCanonicalBaseChange_val k L H ((j.restrictScalars k).comp i)]
  exact geometricComponentBaseChangeEquivOfEmbedding_tower k K L H i j c.val

/-- The corresponding equality of homomorphisms on the entire fixed subgroup. -/
theorem geometricComponentCanonicalBaseChange_tower_hom :
    (geometricComponentFixedTowerIso k K L H).toMonoidHom.comp
        ((geometricComponentCanonicalBaseChange K L (baseChanged k K H)).comp
          (geometricComponentCanonicalBaseChange k K H)) =
      geometricComponentCanonicalBaseChange k L H := by
  apply MonoidHom.ext
  intro c
  exact geometricComponentCanonicalBaseChange_tower k K L H c

end Tower

end Langlands.GroupScheme.IdentityComponent
