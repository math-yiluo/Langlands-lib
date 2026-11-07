import Langlands.GroupScheme.Reductive.RankOneRootCellFactorPairs
import Langlands.GroupScheme.Reductive.SplitIsomorphismCentralizerRootData
import Langlands.GroupScheme.Reductive.PinnedRigidityFromPairs

/-! # Actual opposite factor pairs for split pinned groups -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RankOneRootCellRelation RootCell

variable {k : Type u} [Field k]

/-- In semisimple rank one, every actual nonidentity root point has an
opposite factor pair. -/
theorem exists_oppositeFactorPair_of_rankOne
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (hP : IsRootDatumOf i P)
    (hrank : ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (r : J) (x : rationalPoints G)
    (hx : x ∈ (RelativeRoot.subgroup i (P.root r)).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) : ∃ p, RelativeRoot.IsOppositeFactorPair i (P.root r) x p := by
  have := hG.smooth
  have := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  obtain ⟨xp, xm, hC, hxpRep, -, hxp, hxm, hopen⟩ := rankOne_exists_rootCell
    dynamicCentralizerReductive rankOnePositiveRootUniqueness splitRootLieLine hG hT i
    hi P hP hrank r
  have pair : latticePairing T (P.root r) (P.coroot r) = 2 := by
    rw [← hP.1]
    exact P.root_coroot_two r
  obtain ⟨n, hn⟩ := hP.exists_normalizing_latticeReflectionIso i hT r
  have hn2 := exists_sq_eq_of_isNormalizingPoint hC pair hn
  let D : WeylData k :=
    { G := G, T := T, i := i, xp := xp, xm := xm, α := P.root r, hxp := hxp, hxm := hxm,
      open_cell := hopen, h := P.coroot r, pair := pair, n := n, hn := hn, hn2 := hn2,
      irreducible := DynamicConnected.irreducibleSpace_of_smooth G }
  have hxU := RelativeRoot.subgroup_le_dynamicUnipotent i (P.coroot r)
    (by rw [pair]; norm_num) _ hx
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

/-- A split maximal torus with a supplied root datum has opposite pairs for
all its actual nonidentity root points. -/
theorem hasOppositeFactorPairs_of_rootDatum
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (hP : IsRootDatumOf i P) :
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
  obtain ⟨p, hp⟩ := exists_oppositeFactorPair_of_rankOne hM hT jM hmax Q hQ hdep s
    xM hxMQ hxM1
  change RelativeRoot.IsOppositeFactorPair jM (P.root r) xM p at hp
  have hmiddle : rationalPoints.map m xM = x := hxMx
  refine ⟨(rationalPoints.map m p.1, rationalPoints.map m p.2), ?_⟩
  simpa only [hmiddle] using hp.map m hjM

/-- Every supplied split pinning admits actual normalizing opposite pairs. -/
theorem splitPinnedOppositeFactorPairs : SplitPinnedOppositeFactorPairsStatement.{u} := by
  intro k _ G _ p
  exact hasOppositeFactorPairs_of_rootDatum p.isConnectedReductive p.isSplitTorus
    p.inclusion p.isMaximalTorus p.rootDatum p.isRootDatum

end Langlands.GroupScheme
