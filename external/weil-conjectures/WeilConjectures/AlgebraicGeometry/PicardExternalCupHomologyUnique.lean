/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalCupCochain
import WeilConjectures.Algebra.Homology.TensorKunnethNat

/-! # Uniqueness of normalized external cup on total homology

Source: Stacks Project, Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-homology-unique).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
variable {k : Type w} [Field k] {X Y : Scheme.{w}}

/-- Normalize a family of homology maps on the external tensor cycles.
Source: Stacks, Tag 0BED
(blueprint: lem-sc-picard-external-cup-homology-unique). -/
def IsPicardExternalCupHomology
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (φ : ∀ n : ℕ, (picardExternalTotal f g F G).homology (n : ℤ) ⟶
      (picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).homology (n : ℤ)) : Prop :=
  ∀ (n : ℕ) (i : {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (a : (picardScalarModel f F).cycles (i.val.1 : ℤ))
    (b : (picardScalarModel g G).cycles (i.val.2 : ℤ))
    (z : (picardExternalTotal f g F G).cycles (n : ℤ)),
    (picardExternalTotal f g F G).iCycles (n : ℤ) z =
      HomologicalComplex.ιMapBifunctor (picardScalarModel f F) (picardScalarModel g G)
        (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℤ)
        (i.val.1 : ℤ) (i.val.2 : ℤ) (n : ℤ) (by
          change (i.val.1 : ℤ) + (i.val.2 : ℤ) = (n : ℤ)
          exact_mod_cast i.property)
        (((picardScalarModel f F).iCycles (i.val.1 : ℤ) a) ⊗ₜ[k]
          ((picardScalarModel g G).iCycles (i.val.2 : ℤ) b)) →
    picardScalarModelEquiv (pullback.fst f g ≫ f) (externalCupCoefficients f g F G) n
        (φ n
          ((picardExternalTotal f g F G).homologyπ (n : ℤ) z)) =
      cast (congrArg (fun d ↦ ↥(scalarCohomology (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G) d)) i.property)
        (externalCup f g F G i.val.1 i.val.2
          (picardScalarModelEquiv f F i.val.1
            ((picardScalarModel f F).homologyπ (i.val.1 : ℤ) a))
          (picardScalarModelEquiv g G i.val.2
            ((picardScalarModel g G).homologyπ (i.val.2 : ℤ) b)))

/-- Normalization determines the map on all total homology classes.
Source: Stacks, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-picard-external-cup-homology-unique).

Proof: Tensor Kunneth expresses natural-degree total homology as the direct sum
of the tensors of factor homologies. Lift each factor class through its surjective
homology projection. The Kunneth cycle formula realizes its pure tensor as a total
cycle. Both normalized maps take that cycle to the same external cup class. The
scalar-model comparison is injective, so the images agree. Pure tensors span each
summand and direct-sum inclusions span the direct sum, proving equality. Degree
zero and zero factors are covered by the same argument. -/
theorem picardExternalCupHomology_unique
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules)
    (φ ψ : ∀ n : ℕ, (picardExternalTotal f g F G).homology (n : ℤ) ⟶
      (picardScalarModel (pullback.fst f g ≫ f)
        (externalCupCoefficients f g F G)).homology (n : ℤ))
    (hφ : IsPicardExternalCupHomology f g F G φ)
    (hψ : IsPicardExternalCupHomology f g F G ψ) (n : ℕ) : φ n = ψ n := by
  classical
  let A := picardScalarModel f F
  let B := picardScalarModel g G
  obtain ⟨e, he⟩ := HomologicalComplex.tensor_kunneth_nat A B
    (picardScalarModel_negative f F) (picardScalarModel_negative g G) n
  have h : (φ n).hom.comp e.toLinearMap = (ψ n).hom.comp e.toLinearMap := by
    apply DirectSum.linearMap_ext
    intro i
    apply TensorProduct.ext
    ext x y
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ _)).mp inferInstance x
    obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ _)).mp inferInstance y
    obtain ⟨z, hz, hez⟩ := he i a b
    change φ n (e (DirectSum.lof k _ _ i
      ((A.homologyπ _ a) ⊗ₜ[k] (B.homologyπ _ b)))) =
        ψ n (e (DirectSum.lof k _ _ i
          ((A.homologyπ _ a) ⊗ₜ[k] (B.homologyπ _ b))))
    rw [hez]
    apply (picardScalarModelEquiv (pullback.fst f g ≫ f)
      (externalCupCoefficients f g F G) n).injective
    exact (hφ n i a b z hz).trans (hψ n i a b z hz).symm
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact LinearMap.congr_fun h y

end AlgebraicGeometry.Scheme.Modules
