import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Rational.AlgClosedNormalSolvableTorusStatement
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Nonfixed quotient sections from a noncentral smooth connected subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- If every rational lifted quotient section is fixed by a smooth connected
subgroup, its normal closure lies in the supplied solvable stabilizer and is
central under the explicit normal-solvable-torus statement. -/
theorem isCentral_of_all_quotientLifts_fixed_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (i : H ⟶ G) (j : P ⟶ G) (hj : IsClosedSubgroup j)
    (hP : IsSolvableGroupScheme P) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)
    (hall : ∀ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)) :
    IsCentral i := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : Smooth (G.X ⊗ H.X).hom := smooth_tensor _ _ inferInstance inferInstance
  have : IsReduced (G.X ⊗ H.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k _ (G.X ⊗ H.X).hom
  have hfac : FactorsThrough (SubgroupFunctor.conjugationMap i (𝟙 G)) j := by
    apply UnipotentAllBorelsEnvelope.exists_factor_of_algClosed_points _ hj
    intro x
    let g := x ≫ fst G.X H.X
    let t := x ≫ snd G.X H.X
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    have heq : ((t ≫ i.hom.hom) * g⁻¹) ≫ q = g⁻¹ ≫ q := by
      have h := hall g⁻¹ _ (𝟙 _) t
      simpa only [hu, Category.id_comp, SchemeAction.restrict_act,
        flagQuotientSchemeAction_act_lift] using h
    have hm := (hfib _ g⁻¹ ((t ≫ i.hom.hom) * g⁻¹)).mp heq.symm
    have hprod : x ≫ SubgroupFunctor.conjugationMap i (𝟙 G) =
        g * (t ≫ i.hom.hom) * g⁻¹ := by
      simp only [SubgroupFunctor.conjugationMap, MonObj.comp_mul, GrpObj.comp_inv,
        Grp.id_hom_hom, Category.comp_id, Category.assoc, g, t]
    rw [hprod]
    simpa only [inv_inv, mul_assoc] using hm
  let D := smoothConnectedNormalClosure i
  let e := D.toGeneratedImage.minimalHom j hj hfac
  have he : e ≫ j = D.inclusion := D.toGeneratedImage.minimalHom_comp j hj hfac
  have hec : IsClosedSubgroup e :=
    IsClosedSubgroup.of_comp hj (by rw [he]; exact D.closed)
  have : IsClosedImmersion e.hom.hom.left := hec
  have : Mono e.hom.hom := Over.mono_of_mono_left _
  have : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  have : GeometricallyConnected D.group.X.hom := D.hasSmoothConnectedGeneration.2.2.1
  have : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  have hc : IsCentral D.inclusion :=
    (htorus k G hG D.group D.inclusion D.closed inferInstance inferInstance
      (hP.of_mono e) D.isNormal).2
  intro V x
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (D.contains V ⟨x, rfl⟩)
  change y ≫ D.inclusion.hom.hom = x ≫ i.hom.hom at hy
  rw [← hy]
  exact hc V y

/-- Noncentrality forces an actual rational lift with nonfixed quotient section,
under the explicit normal-solvable-torus input. -/
def nonfixedQuotientLiftOfNoncentralSubgroup_of_structural
    (htorus : AlgClosedReductiveNormalSolvableTorusStatement.{u})
    (hG : IsPseudoReductive G)
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
    (i : H ⟶ G) (hnc : ¬ IsCentral i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  apply Classical.choice
  by_contra hnone
  apply hnc
  apply isCentral_of_all_quotientLifts_fixed_of_structural htorus hG i j hj hP q hfib
  intro g
  by_contra hg
  exact hnone ⟨⟨g, hg⟩⟩

end Langlands.GroupScheme.Dynamic
