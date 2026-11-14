import Langlands.AbelianScheme.CanonicalCreationContraction
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqBottomOperators

/-! # Bottom-degree creation and multiplication-slant contraction -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.CanonicalCreationContraction

open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  (structureCohomology)

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

local instance bottomSectionsAlgebra (X : Over (Spec (CommRingCat.of K)))
    (W : X.left.Opens) : Algebra (CommRingCat.of K) Γ(X.left, W) :=
  (secHom X.hom W).hom.toAlgebra

/-- The actual degree-zero class represented by the constant unit cocycle. -/
def unitClass : structureCohomology A.X 0 :=
  AllSeq.unitCanonical A.X.hom (cover A) (cover_top A) (cover_affine A)

lemma creation_unitClass (x : structureCohomology A.X 1) :
    creation A 0 x (unitClass A) = x :=
  AllSeq.creationCanonical_unitCanonical A.X.hom
    (cover A) (cover_top A) (cover_affine A) x

lemma slant_bottom_pull_left (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 1) :
    slant A ell 0 (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x) =
      ell x • unitClass A :=
  AllSeq.slantByH1Dual_bottom_pull_left (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell x

lemma slant_bottom_pull_right (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 1) :
    slant A ell 0 (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 x) = 0 :=
  AllSeq.slantByH1Dual_bottom_pull_right (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A) (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) ell x

/-- Contraction of an H1 class evaluates the dual times the actual degree-zero unit. -/
theorem contraction_zero (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x : structureCohomology A.X 1) :
    contraction A ell 0 x = ell x • unitClass A := by
  change slant A ell 0
    (pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 1 x) = _
  rw [pullStructure_mul, map_add, slant_bottom_pull_left, slant_bottom_pull_right, add_zero]

/-- Creation after bottom-degree contraction has the expected scalar evaluation. -/
theorem creation_contraction_bottom (ell : structureCohomology A.X 1 →ₗ[K] K)
    (x y : structureCohomology A.X 1) :
    creation A 0 x (contraction A ell 0 y) = ell y • x := by
  rw [contraction_zero, map_smul, creation_unitClass]

end Langlands.AbelianScheme.CanonicalCreationContraction
