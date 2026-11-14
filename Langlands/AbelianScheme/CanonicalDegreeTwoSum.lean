import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqDegreeTwoSum

/-! # The actual degree-two sum map for an abelian variety -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.AbelianScheme.CanonicalDegreeTwoSum

open Langlands.Cohomology Cech
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The simple product cover associated to the fixed finite affine cover of `A`. -/
def productCover : coverIdx A × coverIdx A →
    (A.X ⨯ A.X).left.Opens :=
  prodCover (prod.fst : A.X ⨯ A.X ⟶ A.X).left (prod.snd : A.X ⨯ A.X ⟶ A.X).left
    (cover A) (cover A)

lemma productCover_top : ⨆ j, productCover A j = ⊤ :=
  top_le_iff.mp (iSup_prodOpen_eq_top (cover_spec A).2.2
    (cover_spec A).2.2)

lemma productCover_affine (j) : IsAffineOpen (productCover A j) :=
  isAffineOpen_prodOpen (isPullback_prod A)
    (cover_affine A j.1) (cover_affine A j.2)

/-- Sum of the two actual projection pullbacks and the actual mixed cup. -/
def sumMap :
    (relativeCohomology A.X.hom 2).obj (AllSeq.unitModule A.X.left) ×
      ((relativeCohomology A.X.hom 1).obj (AllSeq.unitModule A.X.left) ⊗[K]
        (relativeCohomology A.X.hom 1).obj (AllSeq.unitModule A.X.left)) ×
      (relativeCohomology A.X.hom 2).obj (AllSeq.unitModule A.X.left) →ₗ[K]
        (relativeCohomology (A.X ⨯ A.X).hom 2).obj (AllSeq.unitModule (A.X ⨯ A.X).left) :=
  AllSeq.degreeTwoSum (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd
    (cover A) (cover A)
    (productCover_top A) (productCover_affine A)

/-- The actual degree-two sum map for an abelian variety is injective. -/
theorem sumMap_injective : Function.Injective (sumMap A) := by
  let _ : ∀ W : A.X.left.Opens, Algebra (CommRingCat.of K) Γ(A.X.left, W) :=
    fun W => (secHom A.X.hom W).hom.toAlgebra
  let _ : ∀ W : (A.X ⨯ A.X).left.Opens,
      Algebra (CommRingCat.of K) Γ((A.X ⨯ A.X).left, W) :=
    fun W => (secHom (A.X ⨯ A.X).hom W).hom.toAlgebra
  exact AllSeq.degreeTwoSum_injective_of_points
    (prod.fst : A.X ⨯ A.X ⟶ A.X) prod.snd (isPullback_prod A)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (cover A) (cover A)
    (cover_top A) (cover_affine A)
    (AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (fun _ => AllSeq.isAffineOpen_inter A.X.hom (cover_affine A))
    (cover_top A) (cover_affine A)
    (productCover_top A) (productCover_affine A) η[A.X] η[A.X]

lemma sumMap_left (x) : sumMap A (x, 0, 0) =
    pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 x := by
  simp only [sumMap, AllSeq.degreeTwoSum_apply, map_zero, add_zero]

lemma sumMap_right (x) : sumMap A (0, 0, x) =
    pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 x := by
  simp only [sumMap, AllSeq.degreeTwoSum_apply, map_zero, zero_add]

end Langlands.AbelianScheme.CanonicalDegreeTwoSum
