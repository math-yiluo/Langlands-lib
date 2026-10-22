import Langlands.Cohomology.Tate.HomologyTransfer

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- The homogeneous transfer is the actual relative norm followed by the coset comparison. -/
lemma homogeneousChainTransfer_mk_single (A : Rep.{u} R G) (n : ℕ)
    (c : Fin (n + 1) → G) (a : A) (r : R) :
    (homogeneousChainTransfer H A).f n
        (Representation.Coinvariants.mk (A ⊗ (Rep.standardComplex R G).X n).ρ
          (a ⊗ₜ[R] MonoidAlgebra.single c r)) =
      ∑ q : G ⧸ H,
        Representation.Coinvariants.mk
          (Rep.res H.subtype A ⊗ (Rep.standardComplex R H).X n).ρ
          (A.ρ q.out⁻¹ a ⊗ₜ[R]
            MonoidAlgebra.single (fun i => cosetCoordinate H (q.out⁻¹ * c i)) r) := by
  classical
  change Representation.Coinvariants.map
      (Rep.res H.subtype A ⊗ Rep.res H.subtype (Rep.diagonal R G (n + 1))).ρ
      (Rep.res H.subtype A ⊗ Rep.diagonal R H (n + 1)).ρ
      ((𝟙 (Rep.res H.subtype A)) ⊗ₘ standardCosetComparisonComponent H n).hom
      (coinvariantsTransfer H (A ⊗ Rep.diagonal R G (n + 1))
        (Representation.Coinvariants.mk (A ⊗ Rep.diagonal R G (n + 1)).ρ
          (a ⊗ₜ[R] MonoidAlgebra.single c r))) = _
  rw [coinvariantsTransfer_mk]
  simp only [inverseCosetSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  change Representation.Coinvariants.mk
      (Rep.res H.subtype A ⊗ Rep.diagonal R H (n + 1)).ρ
      (((𝟙 (Rep.res H.subtype A)) ⊗ₘ standardCosetComparisonComponent H n).hom
        ((A ⊗ Rep.diagonal R G (n + 1)).ρ q.out⁻¹
          (a ⊗ₜ[R] MonoidAlgebra.single c r))) = _
  simp only [Rep.tensor_ρ]
  change Representation.Coinvariants.mk
      (Rep.res H.subtype A ⊗ Rep.diagonal R H (n + 1)).ρ
      (A.ρ q.out⁻¹ a ⊗ₜ[R] (standardCosetComparisonComponent H n).hom
        (Representation.ofMulAction R G (Fin (n + 1) → G) q.out⁻¹
          (MonoidAlgebra.single c r))) = _
  rw [Representation.ofMulAction_single, standardCosetComparisonComponent_single]
  rfl

/-- Inhomogeneous coordinates of the transferred homogeneous tuple. -/
def transferTuple (n : ℕ) (g : Fin n → G) (q : G ⧸ H) : Fin n → H :=
  fun i =>
    (cosetCoordinate H (q.out⁻¹ * Fin.partialProd g i.castSucc))⁻¹ *
      cosetCoordinate H (q.out⁻¹ * Fin.partialProd g i.succ)

/-- The ordinary chain map has the classical coset formula on every generator. -/
lemma ordinaryTransferChainMap_single (A : Rep.{u} R G) (n : ℕ)
    (g : Fin n → G) (a : A) :
    (ordinaryTransferChainMap H A).f n (Finsupp.single g a) =
      ∑ q : G ⧸ H, Finsupp.single (transferTuple H n g q) (A.ρ q.out⁻¹ a) := by
  classical
  change (chainsIsoStandard (Rep.res H.subtype A)).inv.f n
      ((homogeneousChainTransfer H A).f n
        ((chainsIsoStandard A).hom.f n (Finsupp.single g a))) = _
  rw [chainsIsoStandard_hom_single, homogeneousChainTransfer_mk_single, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [chainsIsoStandard_inv_single]
  have hzero : cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 0) = 1 := by
    simpa only [Fin.partialProd_zero, mul_one] using cosetCoordinate_inverse_out H q
  change Finsupp.single (transferTuple H n g q)
      (1 • (Rep.res H.subtype A).ρ
        (cosetCoordinate H (q.out⁻¹ * Fin.partialProd g 0))⁻¹ (A.ρ q.out⁻¹ a)) = _
  rw [hzero, inv_one, map_one]
  simp only [Module.End.one_apply, one_smul]

end Langlands.Tate
