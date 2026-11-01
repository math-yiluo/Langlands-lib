import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Langlands.AbelianScheme.Tate.GeometricTorsionCardinality

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme.Tate

variable {K : Type u} [Field K] (B : AbelianScheme (Spec (.of K))) (n : ℕ)

/-- Actual torsion points are exactly the actual lifts of the unit under
multiplication. -/
def torsionLiftsEquiv :
    GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n ≃
      {z : Spec (.of K) ⟶ B.X.left //
        z ≫ (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left = η[B.X].left} := by
  let f := GroupScheme.multiplication B.toGrp (n : ℤ)
  let h := GroupScheme.kernel_isPullback_scheme f
  refine (torsionSectionsEquiv B n).symm.trans ?_
  exact {
    toFun := fun z => ⟨z.1 ≫ (GroupScheme.kernelι f).hom.hom.left, by
      rw [Category.assoc, h.w, ← Category.assoc, z.2, Category.id_comp]⟩
    invFun := fun z => ⟨h.lift z.1 (𝟙 _) (by simpa [f] using z.2), h.lift_snd _ _ _⟩
    left_inv := fun z => by
      apply Subtype.ext
      apply h.hom_ext
      · exact h.lift_fst _ _ _
      · rw [h.lift_snd, z.2]
    right_inv := fun z => by
      apply Subtype.ext
      exact h.lift_fst _ _ _ }

/-- The actual geometric torsion count is the native rank of multiplication
at the unit point. -/
theorem natCard_level_eq_multiplicationFinrank_at_unit [IsSepClosed K]
    (hn : (n : K) ≠ 0) (x : Spec (.of K)) :
    Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n) =
      (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank
        (η[B.X].left x) := by
  have := multiplicationKernel_isFinite_of_ne_zero B n hn
  have := multiplicationKernel_etale_of_ne_zero B n hn
  have := multiplication_isFinite_of_ne_zero B n hn
  have := multiplication_etale_of_field B n hn
  exact (Nat.card_congr (torsionSectionsEquiv B n).symm).trans
    ((Langlands.AlgebraicGeometry.FiniteEtale.natCard_sections_eq_homFinrank
      (GroupScheme.kernel (GroupScheme.multiplication B.toGrp (n : ℤ))).X.hom x).trans
      (Scheme.Hom.finrank_of_isPullback _ _ _ _
        (GroupScheme.kernel_isPullback_scheme
          (GroupScheme.multiplication B.toGrp (n : ℤ))) x))

/-- Multiplication has constant native rank on the geometrically connected
abelian variety. -/
theorem multiplicationFinrank_eq (hn : (n : K) ≠ 0) (x y : B.X.left) :
    (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank x =
      (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank y := by
  have := multiplication_isFinite_of_ne_zero B n hn
  have := multiplication_etale_of_field B n hn
  let : ConnectedSpace B.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton B.X.hom
  exact (Scheme.Hom.isLocallyConstant_finrank
    (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left).apply_eq_of_preconnectedSpace x y

/-- Over a separably closed field, the actual geometric torsion count is the
native rank of multiplication at any target point. -/
theorem natCard_level_eq_multiplicationFinrank [IsSepClosed K]
    (hn : (n : K) ≠ 0) (y : B.X.left) :
    Nat.card (GroupScheme.Tate.Level B.toGrp (Over.mk (𝟙 (Spec (.of K)))) n) =
      (GroupScheme.multiplication B.toGrp (n : ℤ)).hom.hom.left.finrank y := by
  exact (natCard_level_eq_multiplicationFinrank_at_unit B n hn
    (Classical.arbitrary (Spec (.of K)))).trans (multiplicationFinrank_eq B n hn _ y)

end Langlands.AbelianScheme.Tate
