import Langlands.GroupScheme.Absolute.StronglyRegularGroupOpen
import Langlands.GroupScheme.Rational.QuadraticToralFactorization
import Langlands.GroupScheme.Rational.GeometricPointHom
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Strongly regular points in an open over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuadraticToralReduction

set_option backward.isDefEq.respectTransparency false

/-- Some nonempty open of a connected reductive field group has maximal-torus
centralizers at every rational point. -/
theorem exists_stronglyRegular_fieldOpen (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    ∃ V : Set G.X.left, IsOpen V ∧ V.Nonempty ∧
      ∀ x : rationalPoints G, Set.range x.left ⊆ V →
        ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j ∧ SubgroupFunctor.range j = G.pointCentralizer x := by
  let K := AlgebraicClosure k
  let b := algebraBaseMap k K
  let H := (GroupScheme.baseChange b).obj G
  let π := pullback.fst G.X.hom b
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hH : IsConnectedReductive H := connectedReductiveFieldExtensionStatement k K G hG
  obtain ⟨U, hU, hUne, hreg⟩ := stronglyRegularGroupOpen K H hH
  refine ⟨π '' U, π.isOpenMap _ hU, hUne.image π, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hx ⟨IsLocalRing.closedPoint k, rfl⟩
  let x' := geometricRationalPoint (K := K) G.X x
  have hyr : y ∈ Set.range x'.left := by
    change y ∈ Set.range (geometricRationalPoint (K := K) G.X x).left
    rw [range_geometricRationalPoint]
    exact ⟨_, hxy.symm⟩
  obtain ⟨p, hp⟩ := hyr
  have hx' : Set.range x'.left ⊆ U := by
    rintro z ⟨a, rfl⟩
    have h : a = p := @Subsingleton.elim (PrimeSpectrum K) inferInstance _ _
    rwa [h, hp]
  obtain ⟨T, j, hj, hjc⟩ := hreg x' hx'
  apply exists_maximalTorus_pointCentralizer_of_extension x j hj
  have ht : (baseChangeBasePointsEquiv b G).symm (toUnit (Over.mk b) ≫ x) = x' := by
    rw [show toUnit (Over.mk b) = Over.homMk b (by simp) from toUnit_unique _ _]
    change baseChangeSectionHom b G x = x'
    exact geometricRationalPointHom_apply G x
  rw [ht]
  exact hjc

end Langlands.GroupScheme.QuadraticToralReduction
