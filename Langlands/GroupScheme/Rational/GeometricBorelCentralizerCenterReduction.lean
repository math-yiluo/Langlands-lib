import Langlands.GroupScheme.Rational.GeometricBorelCentralizerCenterStatement
import Langlands.GroupScheme.Absolute.BorelCentralizerCenterStatement
import Langlands.GroupScheme.Absolute.BorelCenterEqualityStatement
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Reductive.CenterBaseChangeProof
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Rational.UnipotentSmoothCenter
import Langlands.GroupScheme.Derived.CenterReduction
import Langlands.GroupScheme.GeometricConnectedness

/-! # The centralizer of a geometric Borel subgroup: reduction to the absolute case -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

/-- The base change of the centralizer of a subgroup functor lies in the centralizer of its
base change. -/
theorem baseChange_centralizer_le_centralizer_baseChange
    {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S} (F : SubgroupFunctor G) :
    F.centralizer.baseChange b ≤ (F.baseChange b).centralizer := by
  intro T x hx
  rw [mem_baseChange, mem_centralizer] at hx
  rw [mem_centralizer]
  intro V a y hy
  rw [mem_baseChange] at hy
  have h1 := hx ((Over.map b).obj V) ((Over.map b).map a) (baseChangePointsEquiv b G V y) hy
  rw [← baseChangePointsEquiv_naturality] at h1
  simpa using h1.map (baseChangePointsEquiv b G V).symm.toMonoidHom

end SubgroupFunctor

/-- Fpqc descent of the inclusion of a centralizer in the centre: if the centre of `G` has a
closed representative and, after a faithfully flat quasi-compact base change, the centralizer
of the image of `i` lies in the centre, then it already does so before base change. -/
theorem centralizer_range_le_center_of_baseChange
    {S S' : Scheme.{u}} (b : S' ⟶ S) [QuasiCompact b] [Flat b] [Surjective b]
    {B G : GroupScheme S} (i : B ⟶ G) (hc : (center G).HasClosedRepresentative)
    (h : (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)).centralizer ≤
      center ((GroupScheme.baseChange b).obj G)) :
    (SubgroupFunctor.range i).centralizer ≤ center G := by
  obtain ⟨Z, z, -, hrep⟩ := hc
  let : Mono z.hom.hom := hrep.1
  have hz : SubgroupFunctor.range z = center G := hrep.2
  rw [← hz]
  apply SubgroupFunctor.le_range_of_baseChange_le b z
  rw [hz, ← center_baseChange]
  refine le_trans (SubgroupFunctor.baseChange_centralizer_le_centralizer_baseChange b _) ?_
  rw [← SubgroupFunctor.range_baseChangeHom]
  exact h

/-- Over any field, Milne 17.22 over the algebraic closure gives `C_G(B) = Z(G)` for a
geometric Borel subgroup `B` of a smooth connected affine group `G`. -/
theorem geometricBorel_centralizer_range_eq_center
    (hCentralizer : BorelCentralizerCenterStatement.{u})
    {k : Type u} [Field k] {G B : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : B ⟶ G) (hi : IsGeometricBorelSubgroup i) :
    (SubgroupFunctor.range i).centralizer = center G := by
  let b := toAlgebraicClosure k
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  apply le_antisymm
  · apply centralizer_range_le_center_of_baseChange b i center_hasClosedRepresentative
    let : Smooth ((GroupScheme.baseChange b).obj G).X.hom :=
      inferInstanceAs (Smooth (pullback.snd G.X.hom b))
    let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
    let : ConnectedSpace ((GroupScheme.baseChange b).obj G).X.left :=
      G.connectedSpace_baseChange_of_smooth_affine b
    exact ((hCentralizer (AlgebraicClosure k) ((GroupScheme.baseChange b).obj G)
      ((GroupScheme.baseChange b).obj B) ((GroupScheme.baseChange b).map i) hi.2).2).le
  · exact SubgroupFunctor.center_le_centralizer _

/-- The reduction of Milne 17.70 to the absolute statements: Proposition 17.22 over every
algebraically closed field and Proposition 17.45 over every field together imply the
statement `Z(B) = C_G(B) = Z(G)` for geometric Borel subgroups over every field. -/
def GeometricBorelCentralizerCenterReductionStatement : Prop :=
  BorelCentralizerCenterStatement.{u} → BorelCenterEqualityStatement.{u} →
    GeometricBorelCentralizerCenterStatement.{u}

/-- Proof of the reduction: point (2) by fpqc descent from the algebraic closure, and point (1)
by rewriting with point (2) and applying Proposition 17.45. -/
theorem geometricBorelCentralizerCenterReduction :
    GeometricBorelCentralizerCenterReductionStatement.{u} := by
  intro hCentralizer hCenter k _ G _ _ _ B i hi
  have heq := geometricBorel_centralizer_range_eq_center hCentralizer i hi
  refine ⟨fun T x => ?_, heq⟩
  rw [heq]
  exact hCenter k G B i hi T x

end Langlands.GroupScheme
