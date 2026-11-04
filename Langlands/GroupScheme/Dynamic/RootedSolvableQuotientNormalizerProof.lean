import Langlands.GroupScheme.Dynamic.FlagQuotientSchemeAction
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.Absolute.NormalSolvableCentrality
import Langlands.GroupScheme.Dynamic.RootedSolvableQuotientNormalizer
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Nonfixed sections and normalizers from normal-solvable centrality -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

attribute [local instance]
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G P H : GroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}

/-- If every rational lifted quotient section is fixed by a smooth connected
subgroup, its normal closure lies in the supplied solvable stabilizer and is
central by normal-solvable centrality. -/
theorem isCentral_of_all_quotientLifts_fixed
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
  let instClosedClosure : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  let instAffineClosure : IsAffineHom D.group.X.hom := by
    rw [← D.inclusion.hom.hom.w]
    infer_instance
  have hc : IsCentral D.inclusion :=
    (hP.of_mono e).isCentral_of_normal_of_isPseudoReductive hG
      D.inclusion D.closed D.isNormal
  intro V x
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (D.contains V ⟨x, rfl⟩)
  change y ≫ D.inclusion.hom.hom = x ≫ i.hom.hom at hy
  rw [← hy]
  exact hc V y

/-- Noncentrality forces an actual rational lift with nonfixed quotient section. -/
def nonfixedQuotientLiftOfNoncentralSubgroup
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
  apply isCentral_of_all_quotientLifts_fixed hG i j hj hP q hfib
  intro g
  by_contra hg
  exact hnone ⟨⟨g, hg⟩⟩

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : Over (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]

variable [IsAlgClosed k]

/-- An actual root supplies a nonfixed rational lift of a solvable quotient. -/
def Dynamic.nonfixedQuotientLiftOfRelativeRoot
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      ¬ ((Dynamic.flagQuotientSchemeAction G (SubgroupFunctor.range j) q hfib).restrict i).IsFixed
        (g ≫ q)} := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth T.toGrp.X.hom := hT.smooth
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  exact Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup hG i
    (not_isCentral_of_relativeRoot i hT hχ) j hj hP q hfib

/-- A noncentral maximal torus factoring through a closed solvable stabilizer
gives a nonidentity Weyl class from smooth proper quotient geometry. -/
def nonidentityNormalizerOfNoncentralSolvableQuotient
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hnc : ¬ IsCentral i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  have : Smooth G.X.hom := hG.smooth
  have : Smooth T.toGrp.X.hom := hi.1.smooth
  have : IsAffineHom T.toGrp.X.hom := hi.2.1.isAffineHom_source
  have : ConnectedSpace T.toGrp.X.left := hi.1.connectedSpace
  let g := Dynamic.nonfixedQuotientLiftOfNoncentralSubgroup
    hG i hnc j hj hP q hfib
  exact nonidentityNormalizerOfNonfixedSmoothProperQuotient i hi j hj f hf hconj
    q hfib g.val g.property

/-- A relative root replaces the noncentrality input in the solvable-quotient
normalizer construction. No supplied movement or nonfixed section is needed. -/
def nonidentityNormalizerOfRootedSolvableQuotient
    (hG : IsPseudoReductive G)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    (j : P ⟶ G) (hj : IsClosedSubgroup j) (hP : IsSolvableGroupScheme P)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P) (q : G.X ⟶ Q)
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V) :
    {w : normalizerPoints i // (QuotientGroup.mk w : relativeWeylGroup i) ≠ 1} := by
  have : Smooth G.X.hom := hG.smooth
  exact nonidentityNormalizerOfNoncentralSolvableQuotient
    hG i hi (not_isCentral_of_relativeRoot i hT hχ)
      j hj hP f hf hconj q hfib

end Langlands.GroupScheme
