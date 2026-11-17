import Langlands.GroupScheme.Torus.RelativeCentralizerReductiveStatement
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.RelativeFieldComparison
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Proof: centralizers of tori in reductive group schemes are reductive -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A relative torus over an algebraically closed field is split. -/
theorem RelativeTorus.IsTorus.isSplitTorus_of_isAlgClosed {k : Type u} [Field k]
    [IsAlgClosed k] {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : RelativeTorus.IsTorus T) : IsSplitTorus T :=
  SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T hT.isTorus

/-- The geometric fibres of a representative of the centralizer of a relative torus in a
reductive group scheme are pseudo-reductive. -/
theorem isPseudoReductive_geometricFiber_of_torusCentralizer {S : Scheme.{u}}
    {G : GroupScheme S} {T : CommGroupScheme S} (t : T.toGrp ⟶ G) (hG : IsReductive G)
    (hT : RelativeTorus.IsTorus T.toGrp) {Z : GroupScheme S} {z : Z ⟶ G}
    (hz : (torusCentralizer t).IsRepresentedBy z) (s : S) :
    IsPseudoReductive (geometricFiber Z s) := by
  let b := geometricPoint S s
  let B := GroupScheme.baseChange b
  have hGs : IsConnectedReductive (geometricFiber G s) :=
    (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed
  have hTs : IsSplitTorus (B.obj T.toGrp) :=
    (hT.baseChange b).isSplitTorus_of_isAlgClosed
  have hzs : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj T)
      (B.map t)).IsRepresentedBy (B.map z) := by
    rw [torusCentralizer_baseChange b t]
    exact hz.baseChange b
  exact (splitTorusCentralizerReductive _ (geometricFiber G s) hGs
    ((CommGroupScheme.baseChange b).obj T) (B.map t) hTs (geometricFiber Z s) (B.map z)
    hzs).isPseudoReductive

/-- **Torus centralizers in reductive group schemes are reductive** (Conrad, *Reductive
group schemes*, p.83). -/
theorem relativeTorusCentralizerReductive :
    RelativeTorusCentralizerReductiveStatement.{u} := by
  intro S G T t hG hT _ht
  have := hG.isAffineHom
  obtain ⟨C, c, hc, hCs, hrep⟩ :=
    relativeTorusCentralizer_hasSmoothClosedRepresentative t hT hG.smooth
  refine ⟨⟨C, c, hc, hrep⟩, ?_⟩
  intro Z z hz
  let e := (Grp.forget _).mapIso (SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy hz hrep)
  exact ⟨smooth_of_over_iso e hCs, isAffineHom_of_over_iso e hc.isAffineHom,
    isPseudoReductive_geometricFiber_of_torusCentralizer t hG hT hz⟩

end Langlands.GroupScheme
