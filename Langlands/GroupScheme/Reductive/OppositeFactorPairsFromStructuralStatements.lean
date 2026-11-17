import Langlands.GroupScheme.Reductive.SplitPinnedOppositeFactorPairs
import Langlands.GroupScheme.Reductive.SplitIsogenyLocalLevis
import Langlands.GroupScheme.Reductive.IsogenyRootRestriction
import Langlands.GroupScheme.Reductive.RankOneCellData
import Langlands.GroupScheme.Reductive.SplitRootRankOneRelations
import Langlands.GroupScheme.Rational.MonicRootParametrization
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellStatement
import Langlands.GroupScheme.Reductive.SplitRootLieLineStatement
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Rational.AlgClosedOppositeFactorPairsStatement
import Langlands.GroupScheme.Torus.SeparablyClosedSplitting
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Opposite factor pairs from supplied rank-one cells and root lines -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

open RankOneRootCellRelation RootCell

variable {k : Type u} [Field k]

/-- In semisimple rank one, with a reduced root datum, supplied rank-one root cells and root
lines give every actual nonidentity root point an opposite factor pair. -/
theorem exists_oppositeFactorPair_of_rankOne_of_structuralStatements
    (hcell : SplitRankOneRootCellStatement.{u}) (hline : SplitRootLieLineStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) [P.IsReduced]
    (hP : IsRootDatumOf i P)
    (hrank : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J) (x : rationalPoints G)
    (hx : x ∈ (RelativeRoot.subgroup i (P.root r)).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) : ∃ p, RelativeRoot.IsOppositeFactorPair i (P.root r) x p := by
  have := hG.smooth
  have := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have hα : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  obtain ⟨xp, xm, hxp, hxm, hopen, -, -⟩ := hcell k G hG T hT i hi J P hP hrank r
  have pair : latticePairing T (P.root r) (P.coroot r) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two r
  have hC := rankOne_centralizer_isRepresentedBy dynamicCentralizerReductive hG hT i hi hrank
    (P.root r) hα (P.coroot r) (by rw [pair]; norm_num)
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT r
  have hn2 := exists_sq_eq_of_isNormalizingPoint hC pair hn
  have : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left := hopen
  have : Mono (Dynamic.tripleCellMultiplication xm i xp) := Over.mono_of_mono_left _
  have : Mono xp.hom.hom := Dynamic.mono_right_of_tripleCell xm i xp
  let D : WeylData k :=
    { G := G, T := T, i := i, xp := xp, xm := xm, α := P.root r, hxp := hxp, hxm := hxm,
      open_cell := hopen, h := P.coroot r, pair := pair, n := n, hn := hn, hn2 := hn2,
      irreducible := DynamicConnected.irreducibleSpace_of_smooth G }
  have hxpEq : VectorGroup.IsTorusEquivariant i xp (P.root r) :=
    VectorGroup.isTorusEquivariant_of_weightPointAction hxp
  have hxpRep : (RelativeRoot.subgroup i (P.root r)).IsRepresentedBy xp :=
    hxpEq.represents_root_of_lie_line hG hT hi hα
      (RelativeRoot.hasNoHigherRoots_of_isRootDatumOf P hT i hP r) (hline k G hG T hT i hi _ hα)
  have hxU := hx
  rw [← hxpRep.2] at hxU
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hxU
  have hv0 : crd v ≠ 0 := by
    intro hvzero
    apply hx1
    rw [← hv, ← gpt_crd v, hvzero, gpt_zero, MonObj.one_comp]
  obtain ⟨c, hc⟩ := (field_base (crd v)).resolve_left hv0
  have hp := D.exists_oppositeFactorPair c
  change ∃ p, RelativeRoot.IsOppositeFactorPair i (P.root r)
    (gpt (c : Γ((base k).left, ⊤)) ≫ xp.hom.hom) p at hp
  rw [hc, gpt_crd, hv] at hp
  exact hp

/-- A split maximal torus with a supplied reduced root datum has opposite pairs for all its
actual nonidentity root points, given supplied rank-one root cells and root lines. -/
theorem hasOppositeFactorPairs_of_rootDatum_of_structuralStatements
    (hcell : SplitRankOneRootCellStatement.{u}) (hline : SplitRootLieLineStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) [P.IsReduced]
    (hP : IsRootDatumOf i P) :
    RelativeRoot.HasOppositeFactorPairs i := by
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro a ha x hx hx1
  rw [relativeRoots_eq_roots, ← hP.2.1] at ha
  obtain ⟨r, rfl⟩ := ha
  have haroot : P.root r ∈ roots i := hP.2.1 ▸ Set.mem_range_self r
  obtain ⟨ζ, hzero, hgeneric⟩ := RootReducedness.exists_cocharacter_pairing_eq_zero
    hT haroot.1 (hT.finite_relativeRoots i)
  let m := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ζ ≫ i)
  have hm := Dynamic.Affine.isRepresentedBy_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ i)
  have hmc := Dynamic.Affine.isClosedSubgroup_centralizerHom
    (CommGroupScheme.groupHom ζ ≫ i)
  have hM := dynamicCentralizerReductive k G hG _ _ m hmc hm
  have := hM.isAffineHom
  have : Mono m.hom.hom := hm.1
  let jM := Dynamic.torusFactor i (CommGroupScheme.groupHom ζ) hm
  have hjM : jM ≫ m = i := Dynamic.torusFactor_comp i _ hm
  have hmax : IsMaximalTorus jM := IsMaximalTorus.of_comp hmc (by rwa [hjM])
  have hroots := dynamicCentralizerRoots k G hG T hT i hi ζ _ m hmc hm hM jM hjM
  have hdep : ∀ β ∈ roots jM, ∀ gamma ∈ roots jM, ¬ LinearIndependent ℤ ![β, gamma] := by
    intro β hβ gamma hgamma
    rw [hroots] at hβ hgamma
    exact RootReducedness.not_linearIndependent_of_not_linearIndependent hT haroot.1 hgamma.1.1
      (hgeneric β hβ.1 hβ.2) (hgeneric gamma hgamma.1 hgamma.2)
  let Q := Langlands.LinearAlgebra.orthogonalRootPairing P ζ
  have hQ : IsRootDatumOf jM Q := hP.orthogonalRootPairing ζ m hm jM hjM hroots
  let s : Langlands.LinearAlgebra.orthogonalIndices P ζ := ⟨r, by
    simpa only [Langlands.LinearAlgebra.orthogonalIndices, Set.mem_ofPred_eq, hP.1] using hzero⟩
  have hmap := LeviGluing.root_map_centralizer i ζ m hm hmc jM hjM hT (P.root r)
    haroot.1 hzero
  rw [← hmap] at hx
  obtain ⟨xM, hxM, hxMx⟩ := SubgroupFunctor.mem_map.mp hx
  have hxM1 : xM ≠ 1 := by
    intro he
    apply hx1
    rw [← hxMx, he, MonObj.one_comp]
  have hxMQ : xM ∈ (RelativeRoot.subgroup jM (Q.root s)).carrier (Over.mk (𝟙 _)) := hxM
  obtain ⟨p, hp⟩ := exists_oppositeFactorPair_of_rankOne_of_structuralStatements hcell hline
    hM hT jM hmax Q hQ hdep s xM hxMQ hxM1
  change RelativeRoot.IsOppositeFactorPair jM (P.root r) xM p at hp
  have hmiddle : rationalPoints.map m xM = x := hxMx
  refine ⟨(rationalPoints.map m p.1, rationalPoints.map m p.2), ?_⟩
  simpa only [hmiddle] using hp.map m hjM

/-- **Opposite factor pairs over algebraically closed fields from structural statements.**
Root-datum existence, rank-one root cells and root lines give
`AlgClosedOppositeFactorPairsStatement`. -/
theorem algClosedOppositeFactorPairs_of_structuralStatements
    (hRD : RootDatumExistenceStatement.{u}) (hcell : SplitRankOneRootCellStatement.{u})
    (hline : SplitRootLieLineStatement.{u}) : AlgClosedOppositeFactorPairsStatement.{u} := by
  intro k _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hmax : IsMaximalTorus i := hi.isMaximalTorus (toriAreSplit_of_isSepClosed k)
  obtain ⟨J, _, P, hP, hred⟩ := hRD k G hG T hT i hmax
  have := hred
  exact hasOppositeFactorPairs_of_rootDatum_of_structuralStatements hcell hline hG hT i hmax
    P hP

namespace RelativeRoot

/-- A chosen opposite factor pair of a nonidentity actual root point, over an algebraically
closed field, from root-datum existence, rank-one root cells and root lines. -/
def oppositeFactorPairOfStructuralStatements
    (hRD : RootDatumExistenceStatement.{u}) (hcell : SplitRankOneRootCellStatement.{u})
    (hline : SplitRootLieLineStatement.{u}) [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {a : characterLattice T}
    (ha : haveI := hG.isAffineHom; haveI := hi.isSplitSubtorus.mono; a ∈ relativeRoots i)
    (x : rationalPoints G)
    (hx : haveI := hG.isAffineHom; haveI := hi.isSplitSubtorus.mono
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) : rationalPoints G × rationalPoints G :=
  haveI := hG.isAffineHom
  haveI := hi.isSplitSubtorus.mono
  Classical.choose
    (algClosedOppositeFactorPairs_of_structuralStatements hRD hcell hline k G hG T i hi a ha x
      hx hx1)

/-- The chosen pair is an opposite factor pair. -/
theorem oppositeFactorPairOfStructuralStatements_spec
    (hRD : RootDatumExistenceStatement.{u}) (hcell : SplitRankOneRootCellStatement.{u})
    (hline : SplitRootLieLineStatement.{u}) [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {a : characterLattice T}
    (ha : haveI := hG.isAffineHom; haveI := hi.isSplitSubtorus.mono; a ∈ relativeRoots i)
    (x : rationalPoints G)
    (hx : haveI := hG.isAffineHom; haveI := hi.isSplitSubtorus.mono
      x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsOppositeFactorPair i a x
      (oppositeFactorPairOfStructuralStatements hRD hcell hline hG hi ha x hx hx1) :=
  haveI := hG.isAffineHom
  haveI := hi.isSplitSubtorus.mono
  Classical.choose_spec
    (algClosedOppositeFactorPairs_of_structuralStatements hRD hcell hline k G hG T i hi a ha x
      hx hx1)

end RelativeRoot

end Langlands.GroupScheme
