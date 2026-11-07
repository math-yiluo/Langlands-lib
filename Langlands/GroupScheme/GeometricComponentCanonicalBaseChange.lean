import Langlands.GroupScheme.GeometricComponentFixedBaseChange

/-! # Canonical base extension of Galois-fixed geometric components -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

private theorem embeddings_differ_by_automorphism
    {k E L : Type u} [Field k] [Field E] [Field L]
    [Algebra k E] [Algebra k L] [Normal k E]
    (i j : E →ₐ[k] L) :
    ∃ σ : E ≃ₐ[k] E, ∀ a : E, j (AlgEquiv.toAlgHom σ a) = i a := by
  refine ⟨@AlgHom.restrictNormal' k _ L L _ _ _ _ (AlgHom.id k L) E _ _
    i.toRingHom.toAlgebra j.toRingHom.toAlgebra
    (IsScalarTower.of_algHom i) (IsScalarTower.of_algHom j) _, ?_⟩
  intro a
  exact @AlgHom.restrictNormal_commutes k _ L L _ _ _ _ (AlgHom.id k L) E _ _
    i.toRingHom.toAlgebra j.toRingHom.toAlgebra
    (IsScalarTower.of_algHom i) (IsScalarTower.of_algHom j) _ a

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The geometric component equivalence with its closure embedding explicit. -/
def geometricComponentBaseChangeEquivOfEmbedding
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    GeometricComponents k H ≃* GeometricComponents K (baseChanged k K H) := by
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeEquiv k K H

/-- Full fixed component extension with its closure embedding explicit. -/
def geometricComponentFixedBaseChangeOfEmbedding
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    geometricComponentFixedSubgroup k H →*
      geometricComponentFixedSubgroup K (baseChanged k K H) := by
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  exact geometricComponentFixedBaseChange k K H

@[simp]
theorem geometricComponentFixedBaseChangeOfEmbedding_val
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (c : geometricComponentFixedSubgroup k H) :
    (geometricComponentFixedBaseChangeOfEmbedding k K H i c).val =
      geometricComponentBaseChangeEquivOfEmbedding k K H i c.val := rfl

private def sectionHomOfEmbedding
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    rationalPoints (baseChanged k (AlgebraicClosure k) H) →*
      rationalPoints (baseChanged K (AlgebraicClosure K) (baseChanged k K H)) := by
  letI := i.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeSectionHom k K H

private theorem sectionHomOfEmbedding_coefficient
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    coefficientBaseChangeEquiv k K (AlgebraicClosure K) H
        (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H)
          (sectionHomOfEmbedding k K H i x)) =
      H.affinePointMap (CommAlgCat.ofHom i)
        (baseChangeCoeffEquiv k (AlgebraicClosure k) H x) := by
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeSectionHom_coefficient k K H x

private theorem equivOfEmbedding_ofPoint
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    geometricComponentBaseChangeEquivOfEmbedding k K H i
        (geometricComponentOfPoint k H x) =
      geometricComponentOfPoint K (baseChanged k K H)
        (sectionHomOfEmbedding k K H i x) := by
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  exact geometricComponentBaseChangeEquiv_ofPoint k K H x

private theorem sectionHomOfEmbedding_conjugate
    (i j : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup k)
    (h : ∀ a : AlgebraicClosure k, j (AlgEquiv.toAlgHom σ a) = i a)
    (x : rationalPoints (baseChanged k (AlgebraicClosure k) H)) :
    sectionHomOfEmbedding k K H j (rationalConjugate k (AlgebraicClosure k) H σ x) =
      sectionHomOfEmbedding k K H i x := by
  apply (baseChangeCoeffEquiv K (AlgebraicClosure K) (baseChanged k K H)).injective
  apply (coefficientBaseChangeEquiv k K (AlgebraicClosure K) H).injective
  rw [sectionHomOfEmbedding_coefficient, sectionHomOfEmbedding_coefficient,
    baseChangeCoeffEquiv_rationalConjugate]
  change Lie.affineMap H j
      (Lie.affineMap H σ.toAlgHom (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)) =
    Lie.affineMap H i (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)
  rw [← Lie.affineMap_comp]
  exact congrArg (fun f => Lie.affineMap H f
    (baseChangeCoeffEquiv k (AlgebraicClosure k) H x)) (AlgHom.ext h)

/-- Changing the closure embedding by a source Galois automorphism changes
exactly the source component by that automorphism. -/
theorem geometricComponentBaseChangeEquivOfEmbedding_conjugate
    (i j : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (σ : Field.absoluteGaloisGroup k)
    (h : ∀ a : AlgebraicClosure k, j (AlgEquiv.toAlgHom σ a) = i a)
    (c : GeometricComponents k H) :
    geometricComponentBaseChangeEquivOfEmbedding k K H j (σ • c) =
      geometricComponentBaseChangeEquivOfEmbedding k K H i c := by
  obtain ⟨x, rfl⟩ := geometricComponentOfPoint_surjective k H c
  rw [geometricComponent_smul_ofPoint, equivOfEmbedding_ofPoint,
    equivOfEmbedding_ofPoint, sectionHomOfEmbedding_conjugate k K H i j σ h]

/-- The map on the full fixed subgroup is independent of the closure embedding. -/
theorem geometricComponentFixedBaseChangeOfEmbedding_independent
    (i j : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    geometricComponentFixedBaseChangeOfEmbedding k K H i =
      geometricComponentFixedBaseChangeOfEmbedding k K H j := by
  obtain ⟨σ, h⟩ := embeddings_differ_by_automorphism i j
  let σ' : Field.absoluteGaloisGroup k := σ
  apply MonoidHom.ext
  intro c
  apply Subtype.ext
  change geometricComponentBaseChangeEquivOfEmbedding k K H i c.val =
    geometricComponentBaseChangeEquivOfEmbedding k K H j c.val
  have hc := geometricComponentBaseChangeEquivOfEmbedding_conjugate k K H i j σ' h c.val
  have hfixed : σ' • c.val = c.val := c.property σ'
  rw [hfixed] at hc
  exact hc.symm

/-- Extend all Galois-fixed components without supplying an embedding between
chosen algebraic closures. Its value is independent of the internally chosen lift. -/
def geometricComponentCanonicalBaseChange :
    geometricComponentFixedSubgroup k H →*
      geometricComponentFixedSubgroup K (baseChanged k K H) :=
  geometricComponentFixedBaseChangeOfEmbedding k K H IsAlgClosed.lift

/-- Every compatible closure embedding computes the canonical map. -/
theorem geometricComponentCanonicalBaseChange_eq_ofEmbedding
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K) :
    geometricComponentCanonicalBaseChange k K H =
      geometricComponentFixedBaseChangeOfEmbedding k K H i :=
  geometricComponentFixedBaseChangeOfEmbedding_independent k K H _ i

/-- The underlying component is the comparison along any closure embedding. -/
theorem geometricComponentCanonicalBaseChange_val
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (c : geometricComponentFixedSubgroup k H) :
    (geometricComponentCanonicalBaseChange k K H c).val =
      geometricComponentBaseChangeEquivOfEmbedding k K H i c.val := by
  rw [geometricComponentCanonicalBaseChange_eq_ofEmbedding k K H i,
    geometricComponentFixedBaseChangeOfEmbedding_val]

/-- The canonical map is injective on the entire Galois-fixed subgroup. -/
theorem geometricComponentCanonicalBaseChange_injective :
    Function.Injective (geometricComponentCanonicalBaseChange k K H) := by
  intro c d h
  apply Subtype.ext
  apply (geometricComponentBaseChangeEquivOfEmbedding k K H IsAlgClosed.lift).injective
  exact congrArg Subtype.val h

/-- The canonical full-fixed map agrees with the earlier rational-class map. -/
theorem geometricComponentCanonicalBaseChange_rational
    (c : RationalComponentQuotient H) :
    geometricComponentCanonicalBaseChange k K H (rationalGeometricComponentToFixed k H c) =
      rationalGeometricComponentBaseChangeToFixed k K H c := by
  let i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  exact geometricComponentFixedBaseChange_rational k K H c

section SpecifiedEmbedding

variable [a : Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)]

/-- With a specified compatible closure algebra, the canonical map agrees with
the previously constructed full-fixed base-change map. -/
theorem geometricComponentCanonicalBaseChange_eq :
    geometricComponentCanonicalBaseChange k K H =
      geometricComponentFixedBaseChange k K H := by
  rw [geometricComponentCanonicalBaseChange_eq_ofEmbedding k K H
    (IsScalarTower.toAlgHom k (AlgebraicClosure k) (AlgebraicClosure K))]
  unfold geometricComponentFixedBaseChangeOfEmbedding
  have ha : (IsScalarTower.toAlgHom k (AlgebraicClosure k)
      (AlgebraicClosure K)).toRingHom.toAlgebra = a := toAlgebra_algebraMap
  congr 1
  exact proof_irrel_heq _ _

end SpecifiedEmbedding

variable {H} {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- Canonical full-fixed base extension is natural in actual group-scheme
homomorphisms, with no supplied embedding of algebraic closures. -/
theorem geometricComponentCanonicalBaseChange_naturality (f : H ⟶ H')
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentCanonicalBaseChange k K H' (geometricComponentFixedMap k f c) =
      geometricComponentFixedMap K ((GroupScheme.baseChange (baseMap k K)).map f)
        (geometricComponentCanonicalBaseChange k K H c) := by
  let i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  rw [geometricComponentCanonicalBaseChange_eq, geometricComponentCanonicalBaseChange_eq]
  exact geometricComponentFixedBaseChange_naturality k K f c

end Langlands.GroupScheme.IdentityComponent
