import Langlands.AbelianScheme.DegreeTwoComparisonAssembly
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCreation
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqAxisSlant

/-! # Creation and multiplication-slant contraction on actual cohomology -/

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

local instance sectionsAlgebra (X : Over (Spec (CommRingCat.of K))) (W : X.left.Opens) :
    Algebra (CommRingCat.of K) Γ(X.left, W) :=
  (secHom X.hom W).hom.toAlgebra

/-- Creation by an actual degree-one class, computed on the fixed affine cover. -/
def creation (n : ℕ) :
    structureCohomology A.X 1 →ₗ[K]
      structureCohomology A.X n →ₗ[K] structureCohomology A.X (n + 1) :=
  AllSeq.creationCanonical A.X.hom (cover A) (cover_top A) (cover_affine A) n

lemma creation_one : creation A 1 = cupA A :=
  AllSeq.creationCanonical_one A.X.hom (cover A) (cover_top A) (cover_affine A)

/-- Slant on the simple product cover by an actual first-factor degree-one dual. -/
def slant (ell : structureCohomology A.X 1 →ₗ[K] K) (n : ℕ) :
    structureCohomology (A.X ⨯ A.X) (n + 1) →ₗ[K] structureCohomology A.X n :=
  AllSeq.slantByH1Dual (isPullback_prod A) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (prod.fst : A.X ⨯ A.X ⟶ A.X).w
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell n

/-- Contraction is multiplication pullback followed by first-factor shuffle slant. -/
def contraction (ell : structureCohomology A.X 1 →ₗ[K] K) (n : ℕ) :
    structureCohomology A.X (n + 1) →ₗ[K] structureCohomology A.X n :=
  (slant A ell n).comp
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) (n + 1))

lemma slant_pull_left (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 2) :
    slant A ell 1 (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 x) = 0 :=
  AllSeq.slantByH1Dual_pull_left (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell x

lemma slant_pull_right (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 2) :
    slant A ell 1 (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 x) = 0 :=
  AllSeq.slantByH1Dual_pull_right (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell x

lemma slant_mixed_cup (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x y : structureCohomology A.X 1) :
    slant A ell 1
      (cupP A (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x)
        (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 y)) = ell x • y := by
  rw [cupP_eq_mixedCover]
  exact AllSeq.slantByH1Dual_mixedCup (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell x y

/-- On cups of degree-one classes, the actual contraction has the exterior formula. -/
theorem contraction_cup (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x y : structureCohomology A.X 1) :
    contraction A ell 1 (cupA A x y) = ell x • y - ell y • x := by
  change slant A ell 1
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 2 (cupA A x y)) = _
  rw [pullStructure_mul_cupA, map_add, map_sub, map_add,
    slant_pull_left, slant_pull_right, slant_mixed_cup, slant_mixed_cup, zero_add, add_zero]

end Langlands.AbelianScheme.CanonicalCreationContraction
