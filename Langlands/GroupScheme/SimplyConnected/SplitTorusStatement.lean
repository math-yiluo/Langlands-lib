import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Maximal split tori of an actual simply connected cover of a semisimple group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, let `π : C ⟶ G` be a supplied simply connected cover of a
semisimple group and `i : S ⟶ G` a maximal split torus. Then there are a commutative group
scheme `S_C`, a maximal split torus `i_C : S_C ⟶ C` and a homomorphism `f : S_C ⟶ S` of
commutative group schemes with `i_C ≫ π = groupHom f ≫ i`, such that `groupHom f` is a central
isogeny (finite, flat, surjective, locally of finite presentation, with central kernel). The
full inverse image of `S` in `C` is not identified with `S_C`. -/
def SimplyConnectedCoverSplitTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G),
    IsSimplyConnectedCover π →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∃ (S_C : CommGroupScheme (Spec (CommRingCat.of k))) (i_C : S_C.toGrp ⟶ C)
        (f : S_C ⟶ S),
        IsMaximalSplitTorus i_C ∧
        i_C ≫ π = CommGroupScheme.groupHom f ≫ i ∧
        IsCentralIsogeny (CommGroupScheme.groupHom f)

end Langlands.GroupScheme
