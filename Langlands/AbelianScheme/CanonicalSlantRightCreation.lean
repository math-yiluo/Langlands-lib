import Langlands.AbelianScheme.CanonicalCreationContraction
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqSlantRightCreation

/-! # Right-axis creation and canonical abelian-scheme slant -/

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

local instance rightSectionsAlgebra (X : Over (Spec (CommRingCat.of K)))
    (W : X.left.Opens) : Algebra (CommRingCat.of K) Γ(X.left, W) :=
  (secHom X.hom W).hom.toAlgebra

/-- Creation on the product, computed on the simple product cover used by slant. -/
def productCreation (n : ℕ) :
    structureCohomology (A.X ⨯ A.X) 1 →ₗ[K]
      structureCohomology (A.X ⨯ A.X) n →ₗ[K]
        structureCohomology (A.X ⨯ A.X) (n + 1) :=
  AllSeq.creationCanonical (A.X ⨯ A.X).hom (mixedCover A)
    (mixedCover_top A) (mixedCover_affine A) n

lemma productCreation_one : productCreation A 1 = cupP A := by
  ext x y
  change AllSeq.creationCanonical (A.X ⨯ A.X).hom (mixedCover A)
    (mixedCover_top A) (mixedCover_affine A) 1 x y = _
  rw [AllSeq.creationCanonical_one, cupP_eq_mixedCover]

/-- The actual first-factor slant anticommutes with right-axis creation in all degrees. -/
theorem slant_creation_right (ell : structureCohomology A.X 1 →ₗ[K] K) (n : ℕ)
    (x : structureCohomology A.X 1)
    (e : structureCohomology (A.X ⨯ A.X) (n + 1)) :
    slant A ell (n + 1)
        (productCreation A (n + 1)
          (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 x) e) =
      -creation A n x (slant A ell n e) :=
  AllSeq.slantCanonical_rightAxisCreationCanonical
    (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (isPullback_prod A) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (AllSeq.h1DualCochainFunctional A.X.hom (cover A) (cover_top A)
      (cover_affine A) (fun _ => rfl) ell)
    (AllSeq.h1DualCochainFunctional_d A.X.hom (cover A) (cover_top A)
      (cover_affine A) (fun _ => rfl) ell)
    (cover_top A) (cover_affine A) (mixedCover_top A) (mixedCover_affine A) n x e

end Langlands.AbelianScheme.CanonicalCreationContraction
