import Langlands.AbelianScheme.CanonicalCreationContraction
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqLeftAxisSlant
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityProof

/-! # The left-axis slant formula for an abelian variety -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.CanonicalCreationContraction

open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

attribute [local instance] sectionsAlgebra

/-- The left axis `a ↦ (0, a)` of `A ⨯ A`. -/
def leftAxis : A.X ⟶ A.X ⨯ A.X :=
  prod.lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X)

lemma leftAxis_left_fst :
    (leftAxis A).left ≫ (prod.fst : A.X ⨯ A.X ⟶ A.X).left = A.X.hom ≫ η[A.X].left := by
  have h := congrArg Over.Hom.left (prod.lift_fst (toUnit A.X ≫ η[A.X]) (𝟙 A.X))
  rw [Over.comp_left, Over.comp_left] at h
  rw [leftAxis, h]
  congr 1

lemma leftAxis_left_snd :
    (leftAxis A).left ≫ (prod.snd : A.X ⨯ A.X ⟶ A.X).left = 𝟙 A.X.left := by
  have h := congrArg Over.Hom.left (prod.lift_snd (toUnit A.X ≫ η[A.X]) (𝟙 A.X))
  rw [Over.comp_left] at h
  rw [leftAxis, h]
  rfl

/-- Creation on `A ⨯ A` by an actual degree-one class, computed on the simple product cover. -/
def creationProd (n : ℕ) :
    structureCohomology (A.X ⨯ A.X) 1 →ₗ[K]
      structureCohomology (A.X ⨯ A.X) n →ₗ[K] structureCohomology (A.X ⨯ A.X) (n + 1) :=
  AllSeq.creationCanonical (A.X ⨯ A.X).hom (mixedCover A) (mixedCover_top A)
    (mixedCover_affine A) n

/-- **The left-axis slant formula.** For an actual dual `ell` of `H¹(A, 𝒪)`, a class
`x ∈ H¹(A, 𝒪)` and any `e ∈ Hⁿ⁺¹(A ⨯ A, 𝒪)`, the slant of the creation `p₁^* x ∪ e` is
`ell x` times the pullback of `e` along the left axis `a ↦ (0, a)`. -/
theorem slant_creationProd_pull_fst (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 1) (n : ℕ) (e : structureCohomology (A.X ⨯ A.X) (n + 1)) :
    slant A ell (n + 1)
        (creationProd A (n + 1) (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x) e) =
      ell x • AllSeq.unitCohomologyPullbackLinear (leftAxis A) (n + 1) e :=
  AllSeq.slantByH1Dual_creation_pull_left (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A)
    η[A.X] (leftAxis A) (leftAxis_left_fst A) (leftAxis_left_snd A)
    (surjective_secHom_top A.X.hom) ell x n e

end Langlands.AbelianScheme.CanonicalCreationContraction
