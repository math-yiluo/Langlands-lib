import Langlands.Group.AlgebraicPolar
import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.Global.InfinitePlaceMatrixRealization

/-! # Normalizing a positive Hermitian form in actual matrix representations -/

noncomputable section

universe u v

open Matrix
open scoped ComplexOrder

namespace Langlands.Group.PositiveFormNormalization

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- The positive square root used to normalize a positive Hermitian form. -/
def normalizingMatrix (J : GL n 𝕜) (hJ : J.val.PosDef) : GL n 𝕜 :=
  AlgebraicPolar.positivePower J hJ (1 / 2)

theorem normalizingMatrix_posDef (J : GL n 𝕜) (hJ : J.val.PosDef) :
    (normalizingMatrix J hJ).val.PosDef :=
  AlgebraicPolar.positivePower_posDef J hJ _

theorem star_normalizingMatrix (J : GL n 𝕜) (hJ : J.val.PosDef) :
    star (normalizingMatrix J hJ) = normalizingMatrix J hJ :=
  Units.ext (normalizingMatrix_posDef J hJ).isHermitian.star_eq

theorem normalizingMatrix_mul_self (J : GL n 𝕜) (hJ : J.val.PosDef) :
    normalizingMatrix J hJ * normalizingMatrix J hJ = J :=
  AlgebraicPolar.positivePower_half_sq J hJ

/-- The adjoint for the form `J` becomes the ordinary adjoint in the new basis. -/
theorem star_conj_normalizingMatrix (J : GL n 𝕜) (hJ : J.val.PosDef) (g : GL n 𝕜) :
    star (normalizingMatrix J hJ * g * (normalizingMatrix J hJ)⁻¹) =
      normalizingMatrix J hJ * (J⁻¹ * star g * J) *
        (normalizingMatrix J hJ)⁻¹ := by
  have hs := star_normalizingMatrix J hJ
  have hsq := normalizingMatrix_mul_self J hJ
  generalize normalizingMatrix J hJ = C at *
  rw [star_mul, star_mul, star_inv, hs, ← hsq]
  group

variable {A : Type v} [Group A]

/-- Normalize a coefficient homomorphism by conjugating with the positive root. -/
def normalizedHom (ρ : A →* GL n 𝕜) (J : GL n 𝕜) (hJ : J.val.PosDef) :
    A →* GL n 𝕜 :=
  (MulAut.conj (normalizingMatrix J hJ)).toMonoidHom.comp ρ

@[simp] theorem normalizedHom_apply (ρ : A →* GL n 𝕜)
    (J : GL n 𝕜) (hJ : J.val.PosDef) (g : A) :
    normalizedHom ρ J hJ g =
      normalizingMatrix J hJ * ρ g * (normalizingMatrix J hJ)⁻¹ := rfl

/-- Stability under the adjoint for a positive form implies ordinary adjoint
stability of the normalized coefficient image. -/
theorem star_mem_normalizedHom_range (ρ : A →* GL n 𝕜)
    (J : GL n 𝕜) (hJ : J.val.PosDef)
    (hform : ∀ g ∈ ρ.range, J⁻¹ * star g * J ∈ ρ.range) :
    ∀ g ∈ (normalizedHom ρ J hJ).range,
      star g ∈ (normalizedHom ρ J hJ).range := by
  rintro g ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hform (ρ x) ⟨x, rfl⟩
  refine ⟨y, ?_⟩
  rw [normalizedHom_apply, hy, normalizedHom_apply]
  exact (star_conj_normalizingMatrix J hJ (ρ x)).symm

end Langlands.Group.PositiveFormNormalization

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [RCLike k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

private def selfSpecPoint :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k)) :=
  Over.homMk (𝟙 _) (by
    rw [algSpec_obj_hom, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _)

/-- Regard an invertible matrix over the base field as an actual base point. -/
def matrixBasePoint (C : GL n k) :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X :=
  selfSpecPoint ≫
    (GeneralLinear.affinePointsEquiv n (CommRingCat.of k) (CommAlgCat.of k k)).symm C

private theorem constantPoint_matrixBasePoint (C : GL n k) :
    (GeneralLinear.groupScheme n (CommRingCat.of k)).constantPoint
        (matrixBasePoint C)
        ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))) =
      (GeneralLinear.affinePointsEquiv n (CommRingCat.of k) (CommAlgCat.of k k)).symm C := by
  unfold constantPoint matrixBasePoint
  have h :
      Over.homMk
          ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k k))).hom
          (Category.comp_id _) ≫
        selfSpecPoint = 𝟙 _ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 _ = 𝟙 _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _
  rw [← Category.assoc, h, Category.id_comp]

/-- Scheme conjugation by a base matrix gives that same conjugation on the
actual coefficient points over the base field. -/
theorem conjugate_matrixBasePoint_affineMatrix (ρ : MatrixRepresentation G n)
    (C : GL n k) (x : G.affinePoints (CommAlgCat.of k k)) :
    (ρ.conjugate (matrixBasePoint C)).affineMatrix (CommAlgCat.of k k) x =
      C * ρ.affineMatrix (CommAlgCat.of k k) x * C⁻¹ := by
  rw [conjugate_affineMatrix, constantPoint_matrixBasePoint, standard_affineMatrix,
    MulEquiv.apply_symm_apply]

/-- A change of basis preserves the scheme-theoretic closed-embedding property. -/
theorem isClosedSubgroup_conjugate (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      (GeneralLinear.groupScheme n (CommRingCat.of k)).X)
    (hρ : IsClosedSubgroup ρ) : IsClosedSubgroup (ρ.conjugate g) := by
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : IsIso
      ((GeneralLinear.groupScheme n (CommRingCat.of k)).innerIso g).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map
      ((GeneralLinear.groupScheme n (CommRingCat.of k)).innerIso g).hom.hom.hom))
  change IsClosedImmersion (ρ.hom.hom.left ≫ _)
  infer_instance

open Langlands.Group.PositiveFormNormalization

/-- Normalize a positive form by an actual group-scheme change of basis. -/
def positiveFormConjugate (ρ : MatrixRepresentation G n)
    (J : GL n k) (hJ : J.val.PosDef) : MatrixRepresentation G n :=
  ρ.conjugate (matrixBasePoint (normalizingMatrix J hJ))

theorem positiveFormConjugate_affineMatrix (ρ : MatrixRepresentation G n)
    (J : GL n k) (hJ : J.val.PosDef) :
    (ρ.positiveFormConjugate J hJ).affineMatrix (CommAlgCat.of k k) =
      normalizedHom (ρ.affineMatrix (CommAlgCat.of k k)) J hJ := by
  apply MonoidHom.ext
  intro x
  exact conjugate_matrixBasePoint_affineMatrix ρ _ x

theorem isClosedSubgroup_positiveFormConjugate (ρ : MatrixRepresentation G n)
    (J : GL n k) (hJ : J.val.PosDef) (hρ : IsClosedSubgroup ρ) :
    IsClosedSubgroup (ρ.positiveFormConjugate J hJ) :=
  ρ.isClosedSubgroup_conjugate _ hρ

/-- The actual normalized representation has an ordinary adjoint-stable
base-field coefficient image. -/
theorem star_mem_positiveFormConjugate_range (ρ : MatrixRepresentation G n)
    (J : GL n k) (hJ : J.val.PosDef)
    (hform : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      J⁻¹ * star g * J ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range) :
    ∀ g ∈ ((ρ.positiveFormConjugate J hJ).affineMatrix (CommAlgCat.of k k)).range,
      star g ∈ ((ρ.positiveFormConjugate J hJ).affineMatrix (CommAlgCat.of k k)).range := by
  rw [positiveFormConjugate_affineMatrix]
  exact star_mem_normalizedHom_range _ J hJ hform

local instance matrixRepresentationPositiveFormInst1 : TopologicalSpace (G.affinePoints (CommAlgCat.of k k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of k k)

/-- Positive-form stability produces an actual closed adjoint-stable
representation with its canonical evaluation-topology closed embedding. -/
theorem exists_closed_starStable_of_positiveForm [IsAffine G.X.left]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (J : GL n k) (hJ : J.val.PosDef)
    (hform : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range,
      J⁻¹ * star g * J ∈ (ρ.affineMatrix (CommAlgCat.of k k)).range) :
    ∃ σ : MatrixRepresentation G n, IsClosedSubgroup σ ∧
      Topology.IsClosedEmbedding (σ.affineMatrix (CommAlgCat.of k k)) ∧
      ∀ g ∈ (σ.affineMatrix (CommAlgCat.of k k)).range,
        star g ∈ (σ.affineMatrix (CommAlgCat.of k k)).range := by
  let σ := ρ.positiveFormConjugate J hJ
  have hσ : IsClosedSubgroup σ := ρ.isClosedSubgroup_positiveFormConjugate J hJ hρ
  exact ⟨σ, hσ, σ.isClosedEmbedding_affineMatrix (CommAlgCat.of k k) hσ,
    ρ.star_mem_positiveFormConjugate_range J hJ hform⟩

end Langlands.GroupScheme.MatrixRepresentation
