import Langlands.GroupScheme.Reductive.RootFactorCell

/-! # Base change of actual ordered factor cells -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RootFactorCell

open RelativeRoot

variable {S S' : Scheme.{u}} (b : S' ⟶ S) {m n : ℕ}
    (A : Fin m → GroupScheme S) (D : GroupScheme S) (B : Fin n → GroupScheme S)

/-- Base change of the actual cell source is the corresponding source of
actual base-changed factors. -/
def sourceBaseChangeIso :
    (Over.pullback b).obj (sourceGroup A D B).X ≅
      (sourceGroup (fun i => (GroupScheme.baseChange b).obj (A i))
        ((GroupScheme.baseChange b).obj D)
        (fun i => (GroupScheme.baseChange b).obj (B i))).X :=
  asIso (prodComparison (Over.pullback b) ((∏ᶜ A).X ⊗ D.X) (∏ᶜ B).X) ≪≫
    tensorIso
      (asIso (prodComparison (Over.pullback b) (∏ᶜ A).X D.X) ≪≫
        tensorIso (finiteProductBaseChangeIso b A) (Iso.refl _))
      (finiteProductBaseChangeIso b B)

variable {G : GroupScheme S}

/-- The negative ordered factor projection commutes with the source comparison. -/
theorem sourceBaseChangeIso_hom_neg (jA : ∀ i, A i ⟶ G) :
    (sourceBaseChangeIso b A D B).hom ≫ fst _ _ ≫ fst _ _ ≫
        orderedMultiplication (fun i => (GroupScheme.baseChange b).map (jA i)) =
      (Over.pullback b).map (fst _ _ ≫ fst _ _ ≫ orderedMultiplication jA) := by
  simp only [sourceBaseChangeIso, Iso.trans_hom, tensorIso_hom, asIso_hom,
    tensorHom_fst_assoc, CartesianMonoidalCategory.prodComparison_fst_assoc, Category.assoc]
  rw [orderedMultiplication_baseChange]
  simp only [Functor.map_comp]

/-- The middle factor projection commutes with the source comparison. -/
theorem sourceBaseChangeIso_hom_middle (jD : D ⟶ G) :
    (sourceBaseChangeIso b A D B).hom ≫ fst _ _ ≫ snd _ _ ≫
        ((GroupScheme.baseChange b).map jD).hom.hom =
      (Over.pullback b).map (fst _ _ ≫ snd _ _ ≫ jD.hom.hom) := by
  simp only [sourceBaseChangeIso, Iso.trans_hom, tensorIso_hom, asIso_hom,
    tensorHom_fst_assoc, tensorHom_snd_assoc, CartesianMonoidalCategory.prodComparison_fst_assoc,
    CartesianMonoidalCategory.prodComparison_snd_assoc, Category.assoc, Iso.refl_hom, Category.id_comp]
  simp only [Functor.map_comp]
  rfl

/-- The positive ordered factor projection commutes with the source comparison. -/
theorem sourceBaseChangeIso_hom_pos (jB : ∀ i, B i ⟶ G) :
    (sourceBaseChangeIso b A D B).hom ≫ snd _ _ ≫
        orderedMultiplication (fun i => (GroupScheme.baseChange b).map (jB i)) =
      (Over.pullback b).map (snd _ _ ≫ orderedMultiplication jB) := by
  simp only [sourceBaseChangeIso, Iso.trans_hom, tensorIso_hom, asIso_hom,
    tensorHom_snd_assoc, CartesianMonoidalCategory.prodComparison_snd_assoc, Category.assoc]
  rw [orderedMultiplication_baseChange]
  simp only [Functor.map_comp]
  rfl

/-- Actual ordered cell multiplication commutes with arbitrary scheme base change. -/
theorem multiplication_baseChange (jA : ∀ i, A i ⟶ G)
    (jD : D ⟶ G) (jB : ∀ i, B i ⟶ G) :
    (sourceBaseChangeIso b A D B).hom ≫
        multiplication (fun i => (GroupScheme.baseChange b).obj (A i))
          ((GroupScheme.baseChange b).obj D) (fun i => (GroupScheme.baseChange b).obj (B i))
          (fun i => (GroupScheme.baseChange b).map (jA i))
          ((GroupScheme.baseChange b).map jD) (fun i => (GroupScheme.baseChange b).map (jB i)) =
      (Over.pullback b).map (multiplication A D B jA jD jB) := by
  simp only [multiplication, MonObj.comp_mul, Functor.map_mul]
  exact congrArg₂ (· * ·)
    (congrArg₂ (· * ·) (sourceBaseChangeIso_hom_neg b A D B jA)
      (sourceBaseChangeIso_hom_middle b A D B jD))
    (sourceBaseChangeIso_hom_pos b A D B jB)

end Langlands.GroupScheme.RootFactorCell
