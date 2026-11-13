import Langlands.GroupScheme.Examples.HermitianMatrixPresentation

/-! # Presentations from injective matrix homomorphisms with exact image -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HermitianMatrix.SchemeModel.Presentation

open SU3Root

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  {Idx : Type v} [Fintype Idx] [DecidableEq Idx]
  (H : Form (fieldInvolution k L) Idx)
  (G : GroupScheme (Spec (CommRingCat.of k)))
  (ρ : ∀ T : Over (Spec (CommRingCat.of k)),
    (T ⟶ G.X) →* Matrix.GeneralLinearGroup Idx
      (SpecialLinear.WeilRoot.tensorAlgebra k L T))
  (hρ_injective : ∀ T, Function.Injective (ρ T))
  (hρ_image : ∀ (T : Over (Spec (CommRingCat.of k)))
    (g : Matrix.GeneralLinearGroup Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)),
    (∃ x : T ⟶ G.X, ρ T x = g) ↔
      ((g : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SU3Root.SchemeModel.coefficientInvolution k L T).bar).transpose *
          (H.gram : Matrix Idx Idx L).map
            (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) *
          (g : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)) =
        (H.gram : Matrix Idx Idx L).map
          (algebraMap L (SpecialLinear.WeilRoot.tensorAlgebra k L T)) ∧
        Matrix.GeneralLinearGroup.det g = 1)
  (hρ_naturality : ∀ {T T' : Over (Spec (CommRingCat.of k))}
    (a : T' ⟶ T) (x : T ⟶ G.X),
    (ρ T' (a ≫ x) : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T')) =
      (ρ T x : Matrix Idx Idx (SpecialLinear.WeilRoot.tensorAlgebra k L T)).map
        (SpecialLinear.WeilRoot.tensorMap k L a))

/-- Injectivity, the full Gram/determinant image equation and all-test matrix
naturality construct a presentation without changing any matrix values. -/
def ofMatrixPoints : Presentation k L H G where
  pointsEquiv T :=
    let f : (T ⟶ G.X) →* tensorPoints k L H T :=
      (ρ T).codRestrict (tensorPoints k L H T)
        (fun x => (hρ_image T (ρ T x)).mp ⟨x, rfl⟩)
    MulEquiv.ofBijective f ⟨
      fun _ _ h => hρ_injective T (congrArg Subtype.val h),
      fun g => by
        obtain ⟨x, hx⟩ := (hρ_image T g.1).mpr g.2
        exact ⟨x, Subtype.ext hx⟩⟩
  matrix_naturality a x := hρ_naturality a x

@[simp] theorem ofMatrixPoints_pointsEquiv_val
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X) :
    ((ofMatrixPoints k L H G ρ hρ_injective hρ_image hρ_naturality).pointsEquiv T x).1 =
      ρ T x := rfl

/-- The inverse equivalence is an actual preimage under the original matrix map. -/
@[simp] theorem ofMatrixPoints_symm_apply
    (T : Over (Spec (CommRingCat.of k))) (g : tensorPoints k L H T) :
    ρ T (((ofMatrixPoints k L H G ρ hρ_injective hρ_image hρ_naturality).pointsEquiv T).symm g) =
      g.1 := by
  have h := ((ofMatrixPoints k L H G ρ hρ_injective hρ_image hρ_naturality).pointsEquiv T).apply_symm_apply g
  exact congrArg Subtype.val h

end Langlands.GroupScheme.HermitianMatrix.SchemeModel.Presentation
