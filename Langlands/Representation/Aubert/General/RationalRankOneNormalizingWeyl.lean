import Langlands.Representation.Aubert.General.RationalRankOneSelfAssociationReduction
import Langlands.Representation.Aubert.General.RationalLeviWeylComparison
import Langlands.Group.RelativeWeylSolomonProof

/-! # Rank-one self-association from a normalizing Weyl element -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Group.RelativeWeylIndexing

universe uB uW uG

section Coxeter

variable {B : Type uB} {W : Type uW} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- If an element outside `W_J` normalizes `W_J` for a maximal subset `J`,
then `J` is its own associated subset. -/
theorem associatedSubset_eq_of_normalizes_of_not_mem [Fintype B] [DecidableEq B] [Fintype W]
    {J : Finset B} {α : B} (hJ : J = Finset.univ.erase α) {w : W}
    (hw : w ∉ standardSubgroup cs J)
    (hnorm : ∀ x ∈ standardSubgroup cs J, w * x * w⁻¹ ∈ standardSubgroup cs J) :
    associatedSubset cs J = J := by
  classical
  obtain ⟨d, hd, hmin⟩ := exists_minimal_in_doubleCoset cs J J w
  obtain ⟨a, ha, b, hb, hdab⟩ := hd
  have hdnorm : ∀ x ∈ standardSubgroup cs J, d * x * d⁻¹ ∈ standardSubgroup cs J := by
    intro x hx
    have h1 : b * x * b⁻¹ ∈ standardSubgroup cs J :=
      (standardSubgroup cs J).mul_mem ((standardSubgroup cs J).mul_mem hb hx)
        ((standardSubgroup cs J).inv_mem hb)
    have h2 := hnorm _ h1
    have he : d * x * d⁻¹ = a * (w * (b * x * b⁻¹) * w⁻¹) * a⁻¹ := by
      rw [hdab]
      group
    rw [he]
    exact (standardSubgroup cs J).mul_mem ((standardSubgroup cs J).mul_mem ha h2)
      ((standardSubgroup cs J).inv_mem ha)
  have hdnot : d ∉ standardSubgroup cs J := by
    intro hdJ
    apply hw
    have he : w = a⁻¹ * d * b⁻¹ := by
      rw [hdab]
      group
    rw [he]
    exact (standardSubgroup cs J).mul_mem
      ((standardSubgroup cs J).mul_mem ((standardSubgroup cs J).inv_mem ha) hdJ)
      ((standardSubgroup cs J).inv_mem hb)
  have hd1 : d⁻¹ ≠ 1 := by
    intro h
    apply hdnot
    rw [inv_eq_one.mp h]
    exact (standardSubgroup cs J).one_mem
  -- Conjugation by `d` maps the finite subgroup `W_J` onto itself.
  have hsurj : ∀ y ∈ standardSubgroup cs J,
      ∃ x ∈ standardSubgroup cs J, d * x * d⁻¹ = y := by
    let S : Finset W := Finset.univ.filter (· ∈ standardSubgroup cs J)
    have hS : ∀ x, x ∈ S ↔ x ∈ standardSubgroup cs J := by
      intro x
      simp [S]
    have hsurjOn := Finset.surjOn_of_injOn_of_card_le (s := S) (t := S)
      (fun x => d * x * d⁻¹)
      (fun x hx => (hS _).mpr (hdnorm x ((hS x).mp hx)))
      (fun x _ y _ hxy => by simpa using hxy)
      le_rfl
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurjOn ((hS y).mpr hy)
    exact ⟨x, (hS x).mp hx, hxy⟩
  have hmin' : IsMinimal cs J J d⁻¹ := isMinimal_inv cs hmin
  have hinvmaps : MapsIntoSimple cs d⁻¹ J J := by
    intro i hi
    obtain ⟨x, hx, hxi⟩ := hsurj _ (simple_mem_standardSubgroup cs hi)
    apply exists_conj_simple_eq_of_isMinimal cs hmin' hi
    have he : d⁻¹ * cs.simple i * d⁻¹⁻¹ = x := by
      rw [← hxi]
      group
    rw [he]
    exact hx
  have hminL : IsMinimal cs J ∅ d⁻¹ := by
    intro a' ha' b' hb'
    rw [standardSubgroup_empty, Subgroup.mem_bot] at hb'
    subst hb'
    simpa using hmin' a' ha' 1 (standardSubgroup cs J).one_mem
  have hpos : positiveSimpleSet cs d⁻¹ = J := by
    have hsub : J ⊆ positiveSimpleSet cs d⁻¹ := by
      intro j hj
      exact (mem_positiveSimpleSet cs d⁻¹ j).mpr
        (((minimalityLengthCriterion_proof cs J J d⁻¹).mp hmin').2 j hj)
    have hne : positiveSimpleSet cs d⁻¹ ≠ Finset.univ := by
      obtain ⟨k, hk⟩ := cs.exists_rightDescent_of_ne_one hd1
      have hdesc := cs.isRightDescent_iff.mp hk
      intro hfull
      have hup := (mem_positiveSimpleSet cs d⁻¹ k).mp (hfull ▸ Finset.mem_univ k)
      omega
    have hsub' : Finset.univ.erase α ⊆ positiveSimpleSet cs d⁻¹ := hJ ▸ hsub
    have hα : α ∉ positiveSimpleSet cs d⁻¹ := by
      intro hα
      apply hne
      apply Finset.eq_univ_of_forall
      intro x
      by_cases hx : x = α
      · rw [hx]
        exact hα
      · exact hsub' (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
    rw [hJ]
    apply Finset.Subset.antisymm _ hsub'
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hα (h ▸ hx), Finset.mem_univ x⟩
  have hlong : d⁻¹ = longestRep cs J :=
    ((longestSurvivor_proof cs) J d⁻¹ hminL).mp (by rw [hpos]; exact hinvmaps)
  have hdlong : (longestRep cs J)⁻¹ = d := by
    rw [← hlong, inv_inv]
  unfold associatedSubset
  rw [hdlong]
  ext j
  simp only [simpleImage, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, hij⟩
    apply mem_of_simple_mem_standardSubgroup cs
    rw [← hij]
    exact hdnorm _ (simple_mem_standardSubgroup cs hi)
  · intro hj
    obtain ⟨i, hi, hij⟩ := hinvmaps j hj
    refine ⟨i, hi, ?_⟩
    rw [← hij]
    group

/-- For a maximal proper subset `J`, the specified longest member of `D(J,∅)`
does not lie in `W_J`. -/
theorem longestRep_not_mem_standardSubgroup [Fintype B] [DecidableEq B] [Fintype W]
    {J : Finset B} {α : B} (hJ : J = Finset.univ.erase α) :
    longestRep cs J ∉ standardSubgroup cs J := by
  intro hmem
  have hminw : IsMinimal cs J ∅ (longestRep cs J) :=
    (mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J)
  have hlen0 : cs.length (longestRep cs J) = 0 := by
    have h := hminw (longestRep cs J)⁻¹ ((standardSubgroup cs J).inv_mem hmem)
      1 (standardSubgroup cs ∅).one_mem
    simpa using h
  obtain ⟨m, hm, hmmin⟩ := exists_minimal_in_doubleCoset cs J ∅ (cs.simple α)
  have hm1 : m = 1 := by
    have hle := length_le_longestRep cs J ((mem_minimalReps cs J ∅ m).mpr hmmin)
    rw [hlen0] at hle
    exact cs.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
  obtain ⟨a, ha, b, hb, hmab⟩ := hm
  rw [standardSubgroup_empty, Subgroup.mem_bot] at hb
  subst hb
  have hsα : cs.simple α = a⁻¹ := by
    rw [hm1, mul_one] at hmab
    exact eq_inv_of_mul_eq_one_right hmab.symm
  have hαJ : α ∈ J := by
    apply mem_of_simple_mem_standardSubgroup cs
    rw [hsα]
    exact (standardSubgroup cs J).inv_mem ha
  rw [hJ] at hαJ
  exact (Finset.notMem_erase α Finset.univ) hαJ

end Coxeter

section ActualQuotient

variable {B : Type uB} {G : Type uG} [Group G]

/-- On the actual normalizer/full-centralizer quotient, a normalizer point
outside a maximal standard Levi that normalizes it forces self-association,
when the Levi contains the full centralizer and its Weyl quotient is the
generated standard Coxeter subgroup. -/
theorem associatedSubset_eq_of_normalizing_point [Fintype B] [DecidableEq B]
    (T : Subgroup G) (L : Finset B → Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    {C : CoxeterMatrix B} (actual : ActualCoxeterSystem T C)
    (hIdent : actualLeviWeylIdentification T L actual)
    {J : Finset B} {α : B} (hJ : J = Finset.univ.erase α)
    (hZ : RelativeWeyl.centralizer T ≤ L J)
    (n : RelativeWeyl.normalizer T)
    (hnorm : ∀ x ∈ L J, (n : G) * x * (n : G)⁻¹ ∈ L J) (hn : (n : G) ∉ L J) :
    associatedSubset actual J = J := by
  apply associatedSubset_eq_of_normalizes_of_not_mem actual hJ
    (w := (QuotientGroup.mk n : RelativeWeyl.Weyl T))
  · rw [← hIdent J]
    rintro ⟨v, hv⟩
    induction v using Quotient.inductionOn' with
    | h y =>
      apply hn
      have hv' : (QuotientGroup.mk (Subgroup.inclusion
          (show RelativeWeyl.normalizerIn T (L J) ≤ RelativeWeyl.normalizer T from
            inf_le_left) y) : RelativeWeyl.Weyl T) = QuotientGroup.mk n := hv
      have hmem := QuotientGroup.eq.mp hv'
      rw [Subgroup.mem_subgroupOf] at hmem
      have hyL : (y : G) ∈ L J := y.property.2
      have hc : ((y : G))⁻¹ * (n : G) ∈ L J := hZ (by simpa using hmem)
      have he : (n : G) = (y : G) * (((y : G))⁻¹ * (n : G)) := by group
      rw [he]
      exact (L J).mul_mem hyL hc
  · intro x hx
    rw [← hIdent J] at hx ⊢
    obtain ⟨v, rfl⟩ := hx
    induction v using Quotient.inductionOn' with
    | h y =>
      refine ⟨QuotientGroup.mk ⟨(n : G) * (y : G) * (n : G)⁻¹, ?_, ?_⟩, ?_⟩
      · exact (RelativeWeyl.normalizer T).mul_mem
          ((RelativeWeyl.normalizer T).mul_mem n.property y.property.1)
          ((RelativeWeyl.normalizer T).inv_mem n.property)
      · exact hnorm _ y.property.2
      · rfl

/-- Under the actual Levi Weyl identification, no lift of the specified
longest representative of a maximal proper subset lies in its Levi. -/
theorem longestLift_not_mem [Fintype B] [DecidableEq B]
    (T : Subgroup G) (L : Finset B → Subgroup G) [Fintype (RelativeWeyl.Weyl T)]
    {C : CoxeterMatrix B} (actual : ActualCoxeterSystem T C)
    (hIdent : actualLeviWeylIdentification T L actual)
    {J : Finset B} {α : B} (hJ : J = Finset.univ.erase α)
    (n : RelativeWeyl.normalizer T) (hn : QuotientGroup.mk n = longestRep actual J) :
    (n : G) ∉ L J := by
  intro hnL
  apply longestRep_not_mem_standardSubgroup actual hJ
  rw [← hn, ← hIdent J]
  exact ⟨QuotientGroup.mk ⟨n, n.property, hnL⟩, rfl⟩

end ActualQuotient

end Langlands.Group.RelativeWeylIndexing

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep Langlands.Group

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {B : Type uI} [Fintype B] [DecidableEq B]
variable (P M U : Finset B → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ J, IsClosed (M J : Set G))
  (hLevi : ∀ (J : Finset B) (I : Finset J), IsSemidirectDecomposition
    ((P (leviIndex J I)).subgroupOf (M J))
    ((M (leviIndex J I)).subgroupOf (M J))
    ((U (leviIndex J I)).subgroupOf (M J)))
  (T : Subgroup G)

/-- The representation-theoretic rank-one conclusion in normalizer form:
reducible cuspidal induction from a maximal standard Levi yields an actual
normalizer point of `T` that normalizes the Levi without belonging to it. -/
def rankOneNormalizingWeyl : Prop :=
  ∀ (J : Finset B), IsMaximalStandard J →
    ∀ (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J)),
      σ.val.IsIrreducible → IsCorollaryLeviCuspidal P M U J (hM J) (hLevi J) hU σ.val →
      ¬ ((normalizedInductionFunctor (h J) (hU J)).obj σ.val).IsIrreducible →
      ∃ n : RelativeWeyl.normalizer T,
        (∀ x ∈ M J, (n : G) * x * (n : G)⁻¹ ∈ M J) ∧ (n : G) ∉ M J

/-- With the actual Levi Weyl identification and full-centralizer containment,
the normalizer form implies the subset equality. -/
theorem rankOneAssociatedSubsetEquality_of_normalizingWeyl
    [Fintype (RelativeWeyl.Weyl T)] {C : CoxeterMatrix B}
    (actual : RelativeWeylIndexing.ActualCoxeterSystem T C)
    (hIdent : RelativeWeylIndexing.actualLeviWeylIdentification T M actual)
    (hZ : ∀ J, RelativeWeyl.centralizer T ≤ M J)
    (hnw : rankOneNormalizingWeyl.{uI, uG, uV} P M U h hU hM hLevi T) :
    rankOneAssociatedSubsetEquality.{uI, uG, uV} P M U h hU hM hLevi T actual := by
  intro J hJ σ hσ hcusp hred
  obtain ⟨α, hα⟩ := hJ
  obtain ⟨n, hnorm, hn⟩ := hnw J ⟨α, hα⟩ σ hσ hcusp hred
  exact RelativeWeylIndexing.associatedSubset_eq_of_normalizing_point
    T M actual hIdent hα (hZ J) n hnorm hn

/-- Conversely, the full self-association target supplies the normalizer
form: any lift of the specified longest representative works. -/
theorem rankOneNormalizingWeyl_of_selfAssociation
    [Fintype (RelativeWeyl.Weyl T)] {C : CoxeterMatrix B}
    (actual : RelativeWeylIndexing.ActualCoxeterSystem T C)
    (hIdent : RelativeWeylIndexing.actualLeviWeylIdentification T M actual)
    (hfull : rankOneSelfAssociation.{uI, uG, uV} P M U h hU hM hLevi T actual) :
    rankOneNormalizingWeyl.{uI, uG, uV} P M U h hU hM hLevi T := by
  intro J hJ σ hσ hcusp hred
  obtain ⟨-, hlift⟩ := hfull J hJ σ hσ hcusp hred
  obtain ⟨α, hα⟩ := hJ
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (RelativeWeylIndexing.longestRep actual J)
  exact ⟨n, fun x hx => (hlift n hn x).mp hx,
    RelativeWeylIndexing.longestLift_not_mem T M actual hIdent hα n hn⟩

end Generic

namespace RationalPointFamily

universe u v

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The rational rank-one normalizing-Weyl obligation, with exactly the
universes, actual families and visible premises of the full target. -/
def RationalRankOneNormalizingWeylStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      letI : DecidableEq (SimpleRoot i ν) := Classical.decEq _
      ∀ [Fintype (Weyl i)]
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (C : CoxeterMatrix (SimpleRoot i ν))
        (actual : ActualCoxeterSystem (torusPoints i) C),
        RootLengthComparison i ν hN hZ actual →
        PositiveSimpleReflectionComparison i ν hN hZ actual →
        actualLeviWeylIdentification (torusPoints i) (levi i ν) actual →
        minimalityLengthCriterion actual → associatedSubsetLaws actual →
        rankOneNormalizingWeyl.{u, u, max (u + 1) v}
          (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
          (h := isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) (hU := hU)
          (hM := hM) (hLevi := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
          (T := torusPoints i)

/-- The normalizing-Weyl obligation proves the full rational self-association
target, through the published subset-equality reduction. -/
theorem rationalRankOneSelfAssociation_of_normalizingWeyl
    (hnw : RationalRankOneNormalizingWeylStatement.{u, v}) :
    RationalRankOneSelfAssociationStatement.{u, v} := by
  apply rationalRankOneSelfAssociation_of_associatedSubsetEquality
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc
  exact rankOneAssociatedSubsetEquality_of_normalizingWeyl
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (torusPoints i) actual hIdent (fun J => pointCentralizer_le_levi i ν hZ J)
    (hnw k G hG T i hi ν hν hStandard hInter hRoots hU hM
      hN hZ C actual hLength hSimple hIdent hMin hAssoc)

/-- The full rational self-association target implies the normalizing-Weyl
statement at the same scope. -/
theorem rationalRankOneNormalizingWeyl_of_selfAssociation
    (hfull : RationalRankOneSelfAssociationStatement.{u, v}) :
    RationalRankOneNormalizingWeylStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro _ hN hZ C actual hLength hSimple hIdent hMin hAssoc
  exact rankOneNormalizingWeyl_of_selfAssociation
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU hM (isSemidirectDecomposition_in_levi i ν hInter hG hi hν)
    (torusPoints i) actual hIdent
    (hfull k G hG T i hi ν hν hStandard hInter hRoots hU hM
      hN hZ C actual hLength hSimple hIdent hMin hAssoc)

/-- At the full rational scope the self-association target and the
normalizing-Weyl statement are equivalent. -/
theorem rationalRankOneSelfAssociation_iff_normalizingWeyl :
    RationalRankOneSelfAssociationStatement.{u, v} ↔
      RationalRankOneNormalizingWeylStatement.{u, v} :=
  ⟨rationalRankOneNormalizingWeyl_of_selfAssociation,
    rationalRankOneSelfAssociation_of_normalizingWeyl⟩

end RationalPointFamily
end Langlands.Aubert.General
