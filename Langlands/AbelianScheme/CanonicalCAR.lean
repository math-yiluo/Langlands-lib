import Langlands.AbelianScheme.CanonicalCARData
import Langlands.AbelianScheme.CanonicalSlantRightCreation
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreationNaturality

/-!
# The canonical anticommutation relation on `H*(A, 𝒪)`

For an abelian scheme `A` over a field `K`, the creation operators `creation A n w` and the
contractions `contraction A ell n` on structure-sheaf cohomology satisfy, in positive degrees,
`contraction ell (creation w e) + creation w (contraction ell e) = ell w • e`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)
open CanonicalCreationContraction

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The multiplication pullback carries creation on `A` to creation on `A ⨯ A`, computed on
`mixedCover A`, in every positive input degree. -/
theorem pullStructure_mul_creation (n : ℕ) (w : structureCohomology A.X 1)
    (e : structureCohomology A.X (n + 1)) :
    pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 2)
        (creation A (n + 1) w e) =
      creationProd A (n + 1)
        (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 1 w)
        (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1) e) := by
  have h := AllSeq.pull_creationCanonical ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd)
    (cover A) (productCover A) Prod.snd (productCover_le_mul A) (cover_top A)
    (productCover_top A) (cover_affine A) (productCover_affine A) n w e
  have hr := AllSeq.creationCanonical_refine (A.X ⨯ A.X).hom (mixedCover A) (productCover A)
    Prod.fst (productCover_le_mixedCover A) (mixedCover_top A) (productCover_top A)
    (mixedCover_affine A) (productCover_affine A) n
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 1 w)
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1) e)
  exact h.trans hr

/-- **The canonical anticommutation relation.** For an actual dual `ell` of `H¹(A, 𝒪)`, a
class `w ∈ H¹(A, 𝒪)` and `e ∈ Hⁿ⁺¹(A, 𝒪)`,
`contraction ell (creation w e) + creation w (contraction ell e) = ell w • e`. -/
theorem contraction_creation_add_creation_contraction
    (ell : structureCohomology A.X 1 →ₗ[K] K) (w : structureCohomology A.X 1) (n : ℕ)
    (e : structureCohomology A.X (n + 1)) :
    contraction A ell (n + 1) (creation A (n + 1) w e) +
      creation A n w (contraction A ell n e) = ell w • e := by
  have hm := pullStructure_mul_creation A n w e
  have hl := slant_creationProd_pull_fst A ell w n
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1) e)
  have hr := slant_creation_right A ell n w
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1) e)
  rw [unitCohomologyPullback_leftAxis_pullStructure_mul] at hl
  change slant A ell (n + 1)
      (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 2)
        (creation A (n + 1) w e)) +
    creation A n w (slant A ell n
      (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1) e)) = ell w • e
  rw [hm, pullStructure_mul, map_add, LinearMap.add_apply, map_add, hl]
  change _ + slant A ell (n + 1) (productCreation A (n + 1) _ _) + _ = _
  rw [hr]
  abel

/-- **The canonical creation-contraction datum.** The actual creation and contraction operators
on `H*(A, 𝒪)`, indexed by the basis `Module.finBasis K H¹(A, 𝒪)` and its coordinate
functionals. -/
def canonicalCARData : CARData.{u, 0} A :=
  CARData.ofBasis A (Module.finBasis K (structureCohomology A.X 1))
    (contraction_creation_add_creation_contraction A)

/-- **The target from the `H¹` dimension.** If `FieldStructureSheafH1DimensionStatement`
holds, then `FieldH2ExteriorCoproductComparisonStatement` holds. -/
theorem fieldH2ExteriorCoproductComparison_of_H1Dimension
    (hH1 : FieldStructureSheafH1DimensionStatement.{u}) :
    FieldH2ExteriorCoproductComparisonStatement.{u} :=
  fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData.{u, 0} hH1 fun _ _ A =>
    ⟨canonicalCARData A⟩

end Langlands.AbelianScheme
