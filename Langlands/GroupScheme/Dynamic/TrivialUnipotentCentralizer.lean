import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.Dynamic.ImproperParabolic
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected

/-! # Trivial contracting subgroups and full centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section Separated

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
  (χ : (Gm S).toGrp ⟶ G)

/-- If the contracting subgroup is trivial on every test, the limit decomposition
identifies the dynamic parabolic with the centralizer. -/
theorem centralizer_eq_parabolic_of_unipotent_eq_bot (hU : unipotent χ = ⊥) :
    centralizer χ = parabolic χ := by
  apply le_antisymm (centralizer_le_parabolic χ)
  intro T g hg
  have hu := mul_inv_limit_mem_unipotent χ ⟨g, hg⟩
  rw [hU, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, mul_inv_eq_one] at hu
  change g = limit χ ⟨g, hg⟩ at hu
  rw [hu]
  exact limit_mem_centralizer χ ⟨g, hg⟩

/-- Canonical isomorphism between actual centralizer and parabolic
representatives when the contracting subgroup is trivial. -/
def centralizerParabolicIsoOfUnipotentEqBot (hU : unipotent χ = ⊥)
    {Z P : GroupScheme S} {iZ : Z ⟶ G} {iP : P ⟶ G}
    (hZ : (centralizer χ).IsRepresentedBy iZ) (hP : (parabolic χ).IsRepresentedBy iP) :
    Z ≅ P :=
  hZ.isoOfIsRepresentedBy (by
    rw [centralizer_eq_parabolic_of_unipotent_eq_bot χ hU]
    exact hP)

/-- The canonical identification respects the inclusions into the ambient
group scheme. -/
theorem centralizerParabolicIsoOfUnipotentEqBot_hom_comp (hU : unipotent χ = ⊥)
    {Z P : GroupScheme S} {iZ : Z ⟶ G} {iP : P ⟶ G}
    (hZ : (centralizer χ).IsRepresentedBy iZ) (hP : (parabolic χ).IsRepresentedBy iP) :
    (centralizerParabolicIsoOfUnipotentEqBot χ hU hZ hP).hom ≫ iP = iZ :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Separated

section Field

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)

/-- A full dynamic parabolic makes its contracting subgroup normal in the
ambient group, so a trivial ground-field unipotent radical kills it whenever
its actual closed representative is unipotent. Smoothness and connectedness of
the representative are supplied by the published dynamic subgroup theorems. -/
theorem unipotent_eq_bot_of_parabolic_eq_top
    (hG : HasTrivialUnipotentRadical G) (hP : parabolic χ = ⊤)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (unipotent χ).IsRepresentedBy j) (hc : IsClosedSubgroup j)
    (hu : IsUnipotent H) : unipotent χ = ⊥ := by
  have hn : (SubgroupFunctor.range j).IsNormal := by
    rw [hj.2]
    change (unipotent χ).IsNormalizedBy ⊤
    rw [← hP]
    exact unipotent_isNormalizedBy_parabolic χ
  rw [← hj.2]
  exact hG H j hc ((dynamicSmooth k G χ H j).2.2 hj)
    (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hj) hu hn

/-- The full-parabolic centrality criterion, reduced to unipotence of an actual
closed contracting-subgroup representative. This theorem retains that
unipotence premise explicitly. -/
theorem parabolic_eq_top_iff_centralizer_eq_top_of_isUnipotent
    (hG : HasTrivialUnipotentRadical G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (unipotent χ).IsRepresentedBy j) (hc : IsClosedSubgroup j)
    (hu : IsUnipotent H) : parabolic χ = ⊤ ↔ centralizer χ = ⊤ := by
  constructor
  · intro hP
    exact (centralizer_eq_parabolic_of_unipotent_eq_bot χ
      (unipotent_eq_bot_of_parabolic_eq_top χ hG hP hj hc hu)).trans hP
  · exact parabolic_eq_top_of_centralizer χ

end Field

end Langlands.GroupScheme.Dynamic
