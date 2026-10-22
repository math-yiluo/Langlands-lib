import Langlands.Cohomology.Tate.CosetTransfer
import Langlands.Cohomology.Tate.StandardChains

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G)

/-- Apply the equivariant coset coordinate map to every homogeneous coordinate. -/
def standardCosetComparisonComponent (n : ℕ) :
    Rep.res H.subtype (Rep.diagonal R G (n + 1)) ⟶
      Rep.diagonal R H (n + 1) :=
  Rep.ofHom
    ⟨MonoidAlgebra.mapDomainLinearMap R R
      (fun c : Fin (n + 1) → G => cosetCoordinate H ∘ c), fun h => by
      apply MonoidAlgebra.lhom_ext'
      intro c
      apply LinearMap.ext_ring
      change MonoidAlgebra.mapDomainLinearMap R R
          (fun c : Fin (n + 1) → G => cosetCoordinate H ∘ c)
          (Representation.ofMulAction R G (Fin (n + 1) → G) (h : G)
            (MonoidAlgebra.single c 1)) =
        Representation.ofMulAction R H (Fin (n + 1) → H) h
          (MonoidAlgebra.mapDomainLinearMap R R
            (fun c : Fin (n + 1) → G => cosetCoordinate H ∘ c)
            (MonoidAlgebra.single c 1))
      rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearMap_single,
        MonoidAlgebra.mapDomainLinearMap_single, Representation.ofMulAction_single]
      congr 1
      funext i
      exact cosetCoordinate_subgroup_mul H h (c i)⟩

lemma standardCosetComparisonComponent_single (n : ℕ) (c : Fin (n + 1) → G) (r : R) :
    (standardCosetComparisonComponent (R := R) H n).hom (MonoidAlgebra.single c r) =
      MonoidAlgebra.single (cosetCoordinate H ∘ c) r :=
  MonoidAlgebra.mapDomainLinearMap_single _ r c

lemma standardCosetComparisonComponent_comm (n : ℕ) :
    Rep.standardComplex.d R H (n + 1) ∘ₗ
        (standardCosetComparisonComponent H (n + 1)).hom.toLinearMap =
      (standardCosetComparisonComponent H n).hom.toLinearMap ∘ₗ
        Rep.standardComplex.d R G (n + 1) := by
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change Rep.standardComplex.d R H (n + 1)
      ((standardCosetComparisonComponent H (n + 1)).hom (MonoidAlgebra.single c 1)) =
    (standardCosetComparisonComponent H n).hom
      (Rep.standardComplex.d R G (n + 1) (MonoidAlgebra.single c 1))
  rw [standardCosetComparisonComponent_single, Rep.standardComplex.d_single,
    Rep.standardComplex.d_single, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact (standardCosetComparisonComponent_single H n (c ∘ p.succAbove)
    (1 * (-1 : R) ^ p.val)).symm

/-- The actual comparison map of homogeneous standard resolutions. -/
def standardCosetComparison :
    ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Rep.standardComplex R G) ⟶ Rep.standardComplex R H where
  f n := standardCosetComparisonComponent H n
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    change ((Rep.standardComplex R H).d (j + 1) j).hom.toLinearMap ∘ₗ
        (standardCosetComparisonComponent H (j + 1)).hom.toLinearMap =
      (standardCosetComparisonComponent H j).hom.toLinearMap ∘ₗ
        ((Rep.standardComplex R G).d (j + 1) j).hom.toLinearMap
    rw [Rep.standardComplex.d_eq, Rep.standardComplex.d_eq]
    exact standardCosetComparisonComponent_comm H j

/-- The comparison preserves the actual augmentation to the trivial module. -/
lemma standardCosetComparison_augmentation :
    standardCosetComparisonComponent (R := R) H 0 ≫ Rep.standardComplex.ε R H =
      (Rep.resFunctor H.subtype).map (Rep.standardComplex.ε R G) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply MonoidAlgebra.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  change (Rep.standardComplex.ε R H).hom
      ((standardCosetComparisonComponent H 0).hom (MonoidAlgebra.single c 1)) =
    (Rep.standardComplex.ε R G).hom (MonoidAlgebra.single c 1)
  rw [standardCosetComparisonComponent_single]
  simp [Rep.standardComplex.ε, MonoidAlgebra.coeff_single]

variable [Fintype (G ⧸ H)]

/-- Relative norm, natural in the resolution variable after tensoring with coefficients. -/
def coinvariantsTensorTransfer (A : Rep.{u} R G) :
    (Rep.coinvariantsTensor R G).obj A ⟶
      Rep.resFunctor H.subtype ⋙ (Rep.coinvariantsTensor R H).obj (Rep.res H.subtype A) where
  app B := ModuleCat.ofHom (coinvariantsTransfer H (A ⊗ B))
  naturality {B C} f := by
    apply ModuleCat.hom_ext
    exact (coinvariantsTransfer_naturality H (A ◁ f)).symm

/-- The transfer chain map on the homogeneous standard resolutions. -/
def homogeneousChainTransfer (A : Rep.{u} R G) :
    (Rep.standardComplex R G).coinvariantsTensorObj A ⟶
      (Rep.standardComplex R H).coinvariantsTensorObj (Rep.res H.subtype A) := by
  let Q := ((Rep.resFunctor H.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Rep.standardComplex R G)
  let t : (Rep.standardComplex R G).coinvariantsTensorObj A ⟶
      Q.coinvariantsTensorObj (Rep.res H.subtype A) :=
    ((coinvariantsTensorTransfer H A).mapHomologicalComplex (ComplexShape.down ℕ)).app
      (Rep.standardComplex R G)
  let c : Q.coinvariantsTensorObj (Rep.res H.subtype A) ⟶
      (Rep.standardComplex R H).coinvariantsTensorObj (Rep.res H.subtype A) :=
    (((Rep.coinvariantsTensor R H).obj (Rep.res H.subtype A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (standardCosetComparison H)
  exact t ≫ c

/-- Ordinary homological transfer, constructed on the actual inhomogeneous chain complexes. -/
def ordinaryTransferChainMap (A : Rep.{u} R G) :
    groupHomology.inhomogeneousChains A ⟶
      groupHomology.inhomogeneousChains (Rep.res H.subtype A) :=
  (chainsIsoStandard A).hom ≫ homogeneousChainTransfer H A ≫
    (chainsIsoStandard (Rep.res H.subtype A)).inv

/-- Ordinary homological transfer induced by the proved chain map. -/
def ordinaryHomologyTransfer (A : Rep.{u} R G) (n : ℕ) :
    groupHomology A n ⟶ groupHomology (Rep.res H.subtype A) n :=
  HomologicalComplex.homologyMap (ordinaryTransferChainMap H A) n

end Langlands.Tate
