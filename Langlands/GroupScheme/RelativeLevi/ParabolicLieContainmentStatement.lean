import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Lie.SubgroupTangent

/-! # Statement: containment of Lie algebras at a point spreads to a Zariski neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Containment of parabolic subgroups from their Lie algebras at a point** (Conrad,
*Reductive group schemes* (2014), Corollary 5.2.7(2), first assertion). Let `G` be a
reductive group scheme over `S`, let `P` and `Q` be parabolic subgroups of `G` containing a
common maximal torus `T` of `G`, and let `s` be a point of `S`. If `Lie(Q_s) ⊆ Lie(P_s)`
inside `Lie(G_s)` over the residue field `κ(s)`, then `Q_V ⊆ P_V` for some Zariski-open
neighbourhood `V` of `s`. -/
def RelativeParabolicLieContainmentStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P Q : GroupScheme S) (i : P ⟶ G) (j : Q ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G) (s : S) (hG : IsReductive G),
    IsRelativeParabolicSubgroup i → IsRelativeParabolicSubgroup j →
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
    SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
    SubgroupFunctor.range t ≤ SubgroupFunctor.range j →
    haveI := hG.isAffineHom
    haveI : IsAffineHom ((GroupScheme.baseChange (S.fromSpecResidueField s :
        Spec (CommRingCat.of (S.residueField s)) ⟶ S)).obj G).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom _))
    (SubgroupFunctor.range (RelativeLevi.residueFiberHom j s)).lie (S.residueField s) ≤
      (SubgroupFunctor.range (RelativeLevi.residueFiberHom i s)).lie (S.residueField s) →
    ∃ V : S.Opens, s ∈ V ∧
      SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map j) ≤
        SubgroupFunctor.range ((GroupScheme.baseChange V.ι).map i)

end Langlands.GroupScheme
