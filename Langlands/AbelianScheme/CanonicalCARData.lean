import Langlands.AbelianScheme.DegreeTwoComparisonFinal
import Langlands.AbelianScheme.CanonicalContractionBottom
import Langlands.AbelianScheme.CanonicalLeftAxisSlant

/-!
# Creation-contraction data from a basis of `H¹(A, 𝒪)`

For an abelian scheme `A` over a field `K`, the actual creation operators `creation A n w` and
contractions `contraction A ell n` on structure-sheaf cohomology form a `CARData` as soon as
they satisfy the positive-degree canonical anticommutation relation
`contraction ell (c_w e) + c_w (contraction ell e) = ell w • e`. The datum uses a basis of
`H¹(A, 𝒪)` and its coordinate functionals. The module also records that the left axis
`a ↦ (0, a)` is a section of the multiplication, so pulling back along it undoes `m^*`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)
open CanonicalCreationContraction

section LeftAxis

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The left axis `a ↦ (0, a)` is a section of the multiplication `m = p₁ * p₂`. -/
lemma leftAxis_comp_mul :
    leftAxis A ≫ ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) = 𝟙 A.X := by
  rw [MonObj.comp_mul, leftAxis, prod.lift_fst, prod.lift_snd, ← Hom.one_def, one_mul]

/-- Pulling back along the left axis undoes the multiplication pullback, in every degree. -/
lemma unitCohomologyPullback_leftAxis_pullStructure_mul (n : ℕ)
    (e : structureCohomology A.X n) :
    AllSeq.unitCohomologyPullbackLinear (leftAxis A) n
        (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) n e) = e := by
  have h := AllSeq.unitCohomologyPullback_comp
    ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (leftAxis A) n
  rw [leftAxis_comp_mul, AllSeq.unitCohomologyPullback_id] at h
  exact (LinearMap.congr_fun h e).symm

end LeftAxis

section Basis

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- **Creation-contraction data from a basis.** Given a basis `b` of `H¹(A, 𝒪)` and the
canonical anticommutation relation for the actual creation and contraction operators in positive
degrees, the operators `c i n = creation A n (b i)` and `d i n = contraction A (b.coord i) n`
form a `CARData`. -/
def CARData.ofBasis {J : Type v} [Fintype J] [DecidableEq J]
    (b : Module.Basis J K (structureCohomology A.X 1))
    (hcar : ∀ (ell : structureCohomology A.X 1 →ₗ[K] K) (w : structureCohomology A.X 1) (n : ℕ)
      (e : structureCohomology A.X (n + 1)),
      contraction A ell (n + 1) (creation A (n + 1) w e) +
        creation A n w (contraction A ell n e) = ell w • e) :
    CARData.{u, v} A where
  I := J
  c i n := creation A n (b i)
  d i n := contraction A (b.coord i) n
  rel i j n := by
    apply LinearMap.ext
    intro e
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, hcar,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  w := b
  span_eq_top := b.span_eq
  c_one i x := by
    rw [creation_one]
  c_zero_d_zero i j := by
    rw [creation_contraction_bottom, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]

/-- Under the positive-degree canonical anticommutation relation, `A` carries a `CARData`,
indexed by `Fin (finrank K H¹(A, 𝒪))`. -/
theorem nonempty_CARData_of_CAR
    (hcar : ∀ (ell : structureCohomology A.X 1 →ₗ[K] K) (w : structureCohomology A.X 1) (n : ℕ)
      (e : structureCohomology A.X (n + 1)),
      contraction A ell (n + 1) (creation A (n + 1) w e) +
        creation A n w (contraction A ell n e) = ell w • e) :
    Nonempty (CARData.{u, 0} A) :=
  ⟨CARData.ofBasis A (Module.finBasis K (structureCohomology A.X 1)) hcar⟩

end Basis

/-- **The target from the `H¹` dimension and the canonical anticommutation relation.** If
`FieldStructureSheafH1DimensionStatement` holds and, for every abelian scheme over a field, the
actual creation and contraction operators satisfy
`contraction ell (creation w e) + creation w (contraction ell e) = ell w • e` in positive
degrees, then `FieldH2ExteriorCoproductComparisonStatement` holds. -/
theorem fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CAR
    (hH1 : FieldStructureSheafH1DimensionStatement.{u})
    (hcar : ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
      (ell : structureCohomology A.X 1 →ₗ[K] K) (w : structureCohomology A.X 1) (n : ℕ)
      (e : structureCohomology A.X (n + 1)),
      contraction A ell (n + 1) (creation A (n + 1) w e) +
        creation A n w (contraction A ell n e) = ell w • e) :
    FieldH2ExteriorCoproductComparisonStatement.{u} :=
  fieldH2ExteriorCoproductComparison_of_H1Dimension_of_CARData.{u, 0} hH1 fun K _ A =>
    nonempty_CARData_of_CAR A (hcar K A)

end Langlands.AbelianScheme
