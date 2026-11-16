import Langlands.GroupScheme.Reductive.CorootCellExtension
import Langlands.GroupScheme.ReducedBaseSmooth.Translation
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof

/-! # Smoothness of a homomorphism from its open-cell restriction -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A homomorphism from a reductive group to a smooth group is smooth when
its restriction to an identity-containing open cell is smooth. -/
theorem smooth_of_smooth_openCell {S : Scheme.{u}} {G H : GroupScheme S}
    {C : Over S} (hG : IsReductive G) (q : G ⟶ H) (j : C ⟶ G.X)
    [IsOpenImmersion j.left] [Smooth H.X.hom] [Smooth (j ≫ q.hom.hom).left]
    (e : 𝟙_ (Over S) ⟶ C) (he : e ≫ j = 1) :
    Smooth q.hom.hom.left := by
  have := hG.smooth
  have : Smooth C.hom := by
    rw [← Over.w j]
    infer_instance
  let p := (j ⊗ₘ j) ≫ μ[G.X]
  have : Smooth p.left := ReducedBaseSmooth.smooth_tensorHom_comp_mul G j
  have : Surjective p.left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    apply ReducedBaseSmooth.range_tensorHom_comp_mul_eq_univ G j
    · intro s
      exact (hG.isConnectedReductive_residueFiber s).smooth
    · intro s
      exact (hG.isConnectedReductive_residueFiber s).connectedSpace
    · rw [MonObj.one_eq_one]
      exact CellGluing.inCell_one_of_comp_eq_one e he (𝟙_ (Over S))
  have htensor : Smooth
      ((j ≫ q.hom.hom) ⊗ₘ (j ≫ q.hom.hom)).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @Smooth) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have hcomp : p ≫ q.hom.hom =
      ((j ≫ q.hom.hom) ⊗ₘ (j ≫ q.hom.hom)) ≫ μ[H.X] := by
    dsimp only [p]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
      tensorHom_comp_tensorHom]
  have : Smooth (p.left ≫ q.hom.hom.left) := by
    change Smooth (p ≫ q.hom.hom).left
    rw [hcomp]
    have := RelativeIdentityComponent.smooth_multiplication H
    change Smooth
      (((j ≫ q.hom.hom) ⊗ₘ (j ≫ q.hom.hom)).left ≫ μ[H.X].left)
    infer_instance
  exact Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp
    p.left q.hom.hom.left

namespace RelativeDerived

open LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} [Finite J] {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {u : J → (Ga R ⟶ G)} {m n : ℕ}
  {neg : Fin m → J} {pos : Fin n → J}
  [IsOpenImmersion (cellMap i u neg pos).left]

/-- Every homomorphism with the required coroot-cell formula is smooth,
without any condition on the base ring. -/
theorem smooth_of_corootCellProjection (hG : IsReductive G)
    (q : G ⟶ (corootQuotient (CommRingCat.of R) P).toGrp)
    (hq : cellMap i u neg pos ≫ q.hom.hom = corootCellProjection R I P m n) :
    Smooth q.hom.hom.left := by
  have : Smooth (corootQuotient (CommRingCat.of R) P).X.hom :=
    (isSplitTorus_corootQuotient (CommRingCat.of R) P).smooth
  have : Smooth (cellMap i u neg pos ≫ q.hom.hom).left := by
    rw [hq]
    exact smooth_corootCellProjection R I P m n
  exact smooth_of_smooth_openCell hG q (cellMap i u neg pos)
    (cellUnit R I m n) (cellUnit_comp_cellMap i u neg pos)

/-- The glued coroot-cell homomorphism is smooth. -/
theorem smooth_corootCellExtension (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    Smooth (corootCellExtension hG hc).hom.hom.left :=
  smooth_of_corootCellProjection hG (corootCellExtension hG hc)
    (cell_comp_corootCellExtension hG hc)

/-- The constructed quotient map with its actual torus restriction,
smoothness and surjectivity, ready for the full-kernel comparison. -/
def smoothCorootCellExtension (hG : IsReductive G)
    (hc : CellGluing.CellCompatible (cellMap i u neg pos)
      (corootCellProjection R I P m n)) :
    {q : G ⟶ (corootQuotient (CommRingCat.of R) P).toGrp //
      i ≫ q = corootProjection (CommRingCat.of R) P ∧
      Smooth q.hom.hom.left ∧ Surjective q.hom.hom.left} :=
  ⟨corootCellExtension hG hc, inclusion_comp_corootCellExtension hG hc,
    smooth_corootCellExtension hG hc, surjective_corootCellExtension hG hc⟩

end RelativeDerived
end Langlands.GroupScheme
