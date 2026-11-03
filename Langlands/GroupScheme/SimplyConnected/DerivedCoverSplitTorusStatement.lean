import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Maximal split tori through the simply connected cover of a derived subgroup -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

/-- Over every field `k`, let `G` be connected reductive with derived subgroup `d : D ⟶ G`
and simply connected cover `π : C ⟶ D`, and let `i : S ⟶ G` be a maximal split torus. Then
there are a maximal split torus `j : S_D ⟶ D` and a closed homomorphism `e : S_D ⟶ S` with
`j ≫ d = groupHom e ≫ i`, together with a maximal split torus `i_C : S_C ⟶ C` and a
homomorphism `f : S_C ⟶ S_D` with `i_C ≫ π = groupHom f ≫ j` and `groupHom f` a central
isogeny. The ambient map to `S` is the composite `f ≫ e`, with
`i_C ≫ π ≫ d = groupHom (f ≫ e) ≫ i`. The rational and real cocharacter maps of `f ≫ e`
are injective with the same image as those of `e`. No surjectivity onto `S` is asserted. -/
def SimplyConnectedDerivedCoverSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D C : GroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ G) (π : C ⟶ D), IsSimplyConnectedDerivedCover d π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∃ (S_D : CommGroupScheme (Spec (CommRingCat.of k))) (j : S_D.toGrp ⟶ D)
        (e : S_D ⟶ S),
        IsMaximalSplitTorus j ∧
        IsClosedSubgroup (CommGroupScheme.groupHom e) ∧
        j ≫ d = CommGroupScheme.groupHom e ≫ i ∧
        ∃ (S_C : CommGroupScheme (Spec (CommRingCat.of k))) (i_C : S_C.toGrp ⟶ C)
          (f : S_C ⟶ S_D),
          IsMaximalSplitTorus i_C ∧
          i_C ≫ π = CommGroupScheme.groupHom f ≫ j ∧
          IsCentralIsogeny (CommGroupScheme.groupHom f) ∧
          i_C ≫ π ≫ d = CommGroupScheme.groupHom (f ≫ e) ≫ i ∧
          Function.Injective ((RealTorusSpace.cocharacterMapInt (f ≫ e)).baseChange ℚ) ∧
          LinearMap.range ((RealTorusSpace.cocharacterMapInt (f ≫ e)).baseChange ℚ) =
            LinearMap.range ((RealTorusSpace.cocharacterMapInt e).baseChange ℚ) ∧
          Function.Injective (RealTorusSpace.cocharacterMapReal (f ≫ e)) ∧
          LinearMap.range (RealTorusSpace.cocharacterMapReal (f ≫ e)) =
            LinearMap.range (RealTorusSpace.cocharacterMapReal e)

end Langlands.GroupScheme
