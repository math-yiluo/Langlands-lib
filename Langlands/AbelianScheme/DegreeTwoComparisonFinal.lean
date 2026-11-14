import Langlands.AbelianScheme.DegreeTwoComparisonAssembly
import Langlands.AbelianScheme.CanonicalDegreeTwoSum
import Langlands.LinearAlgebra.BoundedContractionDetection
import Langlands.AbelianScheme.StructureCohomologyVanishing

/-!
# The degree-two comparison for abelian varieties from a creation-contraction family

The comparison map `degreeTwoMap A` agrees with the injective sum map
`CanonicalDegreeTwoSum.sumMap A`, and alternation of the cup product follows from a bounded
creation-contraction family (`BoundedCreationContraction.cup_self_eq_zero`). Hence
`FieldH2ExteriorCoproductComparisonStatement` follows from such a family on `H*(A, 𝒪)` alone
(`fieldH2ExteriorCoproductComparison_of_CARFamily`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)

section Final

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- `mixedTensorA` is the mixed tensor map of `AllSeq.mixedTensor` on the product cover. -/
lemma mixedTensorA_eq_mixedTensor :
    mixedTensorA A = AllSeq.mixedTensor (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd (cover A)
      (cover A) (CanonicalDegreeTwoSum.productCover_top A)
      (CanonicalDegreeTwoSum.productCover_affine A) := by
  apply TensorProduct.ext'
  intro x y
  rw [mixedTensorA_tmul_eq_mixedCover, AllSeq.mixedTensor_tmul, AllSeq.mixedCup_apply]

/-- The comparison map `degreeTwoMap A` is `CanonicalDegreeTwoSum.sumMap A`. -/
theorem degreeTwoMap_eq_sumMap : degreeTwoMap A = CanonicalDegreeTwoSum.sumMap A := by
  apply LinearMap.ext
  rintro ⟨a, t, b⟩
  rw [degreeTwoMap_apply, CanonicalDegreeTwoSum.sumMap, AllSeq.degreeTwoSum_apply,
    mixedTensorA_eq_mixedTensor]
  exact (add_assoc _ _ _).symm

/-- **Injectivity of the degree-two comparison map.** -/
theorem degreeTwoMap_injective : Function.Injective (degreeTwoMap A) := by
  rw [degreeTwoMap_eq_sumMap]
  exact CanonicalDegreeTwoSum.sumMap_injective A

variable {I : Type v} [Fintype I] [DecidableEq I]
  (c : ∀ (_ : I) (n : ℕ), structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1))
  (d : ∀ (_ : I) (n : ℕ), structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n)
  (hrel : ∀ i j n, (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
    if i = j then LinearMap.id else 0)
  (hbound : ∀ n, Fintype.card I < n → Subsingleton (structureCohomology A.X n))
  (w : I → structureCohomology A.X 1)
  (hspan : Submodule.span K (Set.range w) = ⊤)
  (hcup : ∀ i x, c i 1 x = cupA A (w i) x)
  (hzero : ∀ i j, c j 0 (d i 0 (w j)) = if i = j then w j else 0)

include hrel hbound hspan hcup hzero in
/-- **Alternation of the cup product from a creation-contraction family.** -/
theorem cupA_self_eq_zero_of_CAR (x : structureCohomology A.X 1) : cupA A x x = 0 :=
  Langlands.LinearAlgebra.BoundedCreationContraction.cup_self_eq_zero
    (M := fun n => (structureCohomology A.X n : Type u)) c d hrel hbound (cupA A) (cupA_swap A)
    w hspan hcup hzero x

include hrel hbound hspan hcup hzero in
/-- **The degree-two comparison for `A` from a creation-contraction family.** -/
theorem exists_comparison_of_CAR :
    ∃ (e : structureCohomology A.X 2 ≃ₗ[K] ⋀[K]^2 (structureCohomology A.X 1))
      (κ : structureCohomology (A.X ⨯ A.X) 2 ≃ₗ[K]
        structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
          structureCohomology A.X 2),
      (∀ x, κ (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 x) = (x, 0, 0)) ∧
      (∀ x, κ (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 x) = (0, 0, x)) ∧
      (∀ x, κ (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) *
          (prod.snd : A.X ⨯ A.X ⟶ A.X)) 2 x) =
        (x, exteriorPower.toTensorPower K _ 2 (e x), x)) :=
  exists_comparison_of_inputs A (degreeTwoMap_injective A)
    (cupA_self_eq_zero_of_CAR A c d hrel hbound w hspan hcup hzero) c d hrel hbound w hcup

/-- A **bounded creation-contraction family** on structure-sheaf cohomology `H*(A, 𝒪)`: a finite
index type `I`, creations `c i n : Hⁿ ⟶ Hⁿ⁺¹` and contractions `d i n : Hⁿ⁺¹ ⟶ Hⁿ` satisfying the
canonical anticommutation relations, vanishing of `Hⁿ` above `card I`, and spanning vectors
`w i ∈ H¹` such that `c i 1` is the cup product with `w i` and the degree-zero formulas hold. -/
structure CARFamily where
  /-- The index type. -/
  I : Type v
  [fintype : Fintype I]
  [decEq : DecidableEq I]
  /-- Creation operators. -/
  c : ∀ (_ : I) (n : ℕ), structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1)
  /-- Contraction operators. -/
  d : ∀ (_ : I) (n : ℕ), structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n
  rel : ∀ i j n, (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
    if i = j then LinearMap.id else 0
  bound : ∀ n, Fintype.card I < n → Subsingleton (structureCohomology A.X n)
  /-- The degree-one vectors. -/
  w : I → structureCohomology A.X 1
  span_eq_top : Submodule.span K (Set.range w) = ⊤
  c_one : ∀ i x, c i 1 x = cupA A (w i) x
  c_zero_d_zero : ∀ i j, c j 0 (d i 0 (w j)) = if i = j then w j else 0

attribute [instance] CARFamily.fintype CARFamily.decEq

/-- **The degree-two comparison for `A` from a creation-contraction family.** -/
theorem exists_comparison_of_CARFamily (F : CARFamily.{u, v} A) :
    ∃ (e : structureCohomology A.X 2 ≃ₗ[K] ⋀[K]^2 (structureCohomology A.X 1))
      (κ : structureCohomology (A.X ⨯ A.X) 2 ≃ₗ[K]
        structureCohomology A.X 2 × (⨂[K]^2 (structureCohomology A.X 1)) ×
          structureCohomology A.X 2),
      (∀ x, κ (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 x) = (x, 0, 0)) ∧
      (∀ x, κ (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 x) = (0, 0, x)) ∧
      (∀ x, κ (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) *
          (prod.snd : A.X ⨯ A.X ⟶ A.X)) 2 x) =
        (x, exteriorPower.toTensorPower K _ 2 (e x), x)) :=
  exists_comparison_of_CAR A F.c F.d F.rel F.bound F.w F.span_eq_top F.c_one F.c_zero_d_zero

end Final

/-- **The target from creation-contraction families.** If structure-sheaf cohomology of every
abelian scheme over a field carries a `CARFamily`, then
`FieldH2ExteriorCoproductComparisonStatement` holds. -/
theorem fieldH2ExteriorCoproductComparison_of_CARFamily
    (h : ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
      Nonempty (CARFamily.{u, v} A)) :
    FieldH2ExteriorCoproductComparisonStatement.{u} := by
  intro K _ A
  exact exists_comparison_of_CARFamily A (h K A).some

section H1Dimension

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- Spanning vectors bound the dimension of `H¹(A, 𝒪)`. -/
theorem finrank_structureCohomology_one_le_card {I : Type v} [Fintype I]
    (w : I → structureCohomology A.X 1) (hspan : Submodule.span K (Set.range w) = ⊤) :
    Module.finrank K (structureCohomology A.X 1) ≤ Fintype.card I := by
  have h := finrank_range_le_card (R := K) w
  rwa [Set.finrank, hspan, finrank_top] at h

/-- A **creation-contraction datum** on `H*(A, 𝒪)`: all fields of `CARFamily` except the degree
bound. -/
structure CARData where
  /-- The index type. -/
  I : Type v
  [fintype : Fintype I]
  [decEq : DecidableEq I]
  /-- Creation operators. -/
  c : ∀ (_ : I) (n : ℕ), structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1)
  /-- Contraction operators. -/
  d : ∀ (_ : I) (n : ℕ), structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n
  rel : ∀ i j n, (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
    if i = j then LinearMap.id else 0
  /-- The degree-one vectors. -/
  w : I → structureCohomology A.X 1
  span_eq_top : Submodule.span K (Set.range w) = ⊤
  c_one : ∀ i x, c i 1 x = cupA A (w i) x
  c_zero_d_zero : ∀ i j, c j 0 (d i 0 (w j)) = if i = j then w j else 0

attribute [instance] CARData.fintype CARData.decEq

/-- Under `FieldStructureSheafH1DimensionStatement`, a creation-contraction datum is a
`CARFamily`: `Hⁿ(A, 𝒪) = 0` for `n > card I`, since `card I ≥ dim H¹(A, 𝒪) = g`. -/
def CARData.toCARFamily (hH1 : FieldStructureSheafH1DimensionStatement.{u})
    (D : CARData.{u, v} A) : CARFamily.{u, v} A where
  I := D.I
  c := D.c
  d := D.d
  rel := D.rel
  bound n hn := subsingleton_structureCohomology_of_finrank_lt_of_H1Dimension A hH1 n
    ((finrank_structureCohomology_one_le_card A D.w D.span_eq_top).trans_lt hn)
  w := D.w
  span_eq_top := D.span_eq_top
  c_one := D.c_one
  c_zero_d_zero := D.c_zero_d_zero

end H1Dimension

/-- **The target from the `H¹` dimension and creation-contraction data.** If
`FieldStructureSheafH1DimensionStatement` holds and structure-sheaf cohomology of every abelian
scheme over a field carries a `CARData`, then `FieldH2ExteriorCoproductComparisonStatement`
holds. -/
theorem fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData
    (hH1 : FieldStructureSheafH1DimensionStatement.{u})
    (h : ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
      Nonempty (CARData.{u, v} A)) :
    FieldH2ExteriorCoproductComparisonStatement.{u} :=
  fieldH2ExteriorCoproductComparison_of_CARFamily.{u, v} fun K _ A =>
    ⟨(h K A).some.toCARFamily A hH1⟩

end Langlands.AbelianScheme
