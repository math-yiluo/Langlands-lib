import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGraph
import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneClosure
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.CentralizerRootSupport

/-! # Actual rank-one root factors and their local three-factor cells -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.LeviGluing

section PositiveCone

variable {I M : Type*} [Fintype I] [AddCommGroup M]
    {v : I → M} (hv : LinearIndependent ℤ v)

include hv in
/-- A nonzero element of an independent nonnegative cone dependent with one
of its generators is a strictly positive integral multiple of that generator. -/
theorem exists_pos_nsmul_of_mem_positiveClosure
    (a : I) {x : M} (hx : x ∈ AddSubmonoid.closure (Set.range v))
    (hx0 : x ≠ 0) (hdep : ¬ LinearIndependent ℤ ![v a, x]) :
    ∃ n : ℕ, 0 < n ∧ n • v a = x := by
  classical
  obtain ⟨c, hc⟩ := AddSubmonoid.exists_of_mem_closure_range v _ hx
  rw [LinearIndependent.pair_iff] at hdep
  push Not at hdep
  obtain ⟨s, t, hst, hne⟩ := hdep
  let d : I → ℤ := fun j => s * (Pi.single a (1 : ℤ) : I → ℤ) j + t * (c j : ℤ)
  have hd : ∑ j, d j • v j = 0 := by
    simp only [d, add_smul, mul_smul, Finset.sum_add_distrib,
      ← Finset.smul_sum]
    simpa only [Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, natCast_zsmul, hc] using hst
  have hcoef (j : I) : d j = 0 := by
    have h := Fintype.linearIndependent_iffₛ.mp hv d (fun _ => 0)
      (by simpa using hd) j
    exact h
  have ht : t ≠ 0 := by
    intro ht
    have hs := hcoef a
    simp only [d, Pi.single_eq_same, mul_one, ht, zero_mul, add_zero] at hs
    exact hne hs ht
  have hc0 (j : I) (hj : j ≠ a) : c j = 0 := by
    have h := hcoef j
    simp only [d, Pi.single_eq_of_ne hj, mul_zero, zero_add] at h
    exact Int.natCast_eq_zero.mp ((mul_eq_zero.mp h).resolve_left ht)
  have hsum : ∑ j, c j • v j = c a • v a := by
    apply Finset.sum_eq_single a
    · intro j _ hj
      rw [hc0 j hj, zero_smul]
    · simp
  have heq : c a • v a = x := hsum.symm.trans hc.symm
  refine ⟨c a, ?_, heq⟩
  by_contra h
  have hca : c a = 0 := by omega
  exact hx0 (by simpa only [hca, zero_smul] using heq.symm)

end PositiveCone

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : T.toGrp ⟶ G)
    {J : Type v}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (ν : cocharacterLattice T)
    (hT : IsSplitTorus T.toGrp) (hν : IsGenericCocharacter i ν)

include hP hT hν in
/-- An actual positive root dependent with a simple root is a strictly positive
integral multiple of that simple root, including in a nonreduced root datum. -/
theorem positiveRoot_eq_pos_nsmul_of_dependent
    (a : simpleRelativeRoots i ν) {β : characterLattice T}
    (hβ : β ∈ positiveRelativeRoots i ν)
    (hdep : ¬ LinearIndependent ℤ ![(a : characterLattice T), β]) :
    ∃ n : ℕ, 0 < n ∧ n • (a : characterLattice T) = β := by
  classical
  let : Fintype (simpleRelativeRoots i ν) :=
    (hT.finite_simpleRelativeRoots i ν).fintype
  apply exists_pos_nsmul_of_mem_positiveClosure
    (linearIndependent_simpleRoots i P hP ν hT hν) a _ hβ.1.1 hdep
  rw [Subtype.range_coe, closure_simpleRoots_eq_positive i P hP ν hT]
  exact AddSubmonoid.subset_closure hβ

section RootFactors

variable {L : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom L.X.hom] [Smooth L.X.hom] [ConnectedSpace L.X.left]

include hT in
/-- Matching the actual positive roots with a single integral ray identifies
an entire dynamic unipotent functor, rather than only its rational points. -/
theorem unipotent_eq_root_of_positiveRoots_on_ray
    (t : T.toGrp ⟶ L) (ch : cocharacterLattice T) (α : characterLattice T)
    (hα : 0 < latticePairing T α ch)
    (hray : ∀ β ∈ relativeRoots t, 0 < latticePairing T β ch →
      ∃ n : ℕ, 0 < n ∧ n • α = β) :
    Dynamic.unipotent (CommGroupScheme.groupHom ch ≫ t) = RelativeRoot.subgroup t α := by
  have htail : RelativeRoot.cyclicTail α 1 ≤ RelativeRoot.positiveSemigroup ch := by
    rintro β ⟨n, _, hn, rfl⟩
    change 0 < latticePairing T (n • α) ch
    simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] using
      mul_pos (Int.natCast_pos.mpr hn) hα
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp only [map_zero, LinearMap.zero_apply, lt_self_iff_false] at hα
  rw [(RelativeRoot.dynamicSemigroupComparison k L inferInstance inferInstance
    inferInstance T hT t ch).2.2]
  calc
    _ = RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation t)
        (RelativeRoot.cyclicTail α 1) := by
      apply RelativeRoot.semigroupSubgroup_eq_of_relativeRoot_iff t
      · constructor
        · intro h
          simp only [RelativeRoot.positiveSemigroup, AddSubsemigroup.mem_mk,
            Set.mem_ofPred_eq, map_zero, LinearMap.zero_apply, lt_self_iff_false] at h
        · intro h
          have h' := htail h
          simp only [RelativeRoot.positiveSemigroup, AddSubsemigroup.mem_mk,
            Set.mem_ofPred_eq, map_zero, LinearMap.zero_apply, lt_self_iff_false] at h'
      · intro β hβ
        constructor
        · intro hpos
          obtain ⟨n, hn, heq⟩ := hray β hβ hpos
          exact ⟨n, by omega, hn, heq⟩
        · exact fun h => htail h
    _ = RelativeRoot.subgroup t α :=
      RelativeRoot.weightFiltration_one_eq_subgroup hT t α hα0

variable (ζ : cocharacterLattice T) (hζ : IsRankOneDirection i ζ)
    (a : simpleRelativeRoots i ν) (haζ : latticePairing T (a : characterLattice T) ζ = 0)
    (z : L ⟶ G)
    (hz : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy z)
    (t : T.toGrp ⟶ L) (ht : t ≫ z = i)

include hP hT hν hζ haζ hz ht in
/-- The positive chamber factor in the actual simple-root Levi is exactly the
full intrinsic root functor for the chosen simple root. -/
theorem rankOne_unipotent_eq_positiveRoot :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t) =
      RelativeRoot.subgroup t (a : characterLattice T) := by
  apply unipotent_eq_root_of_positiveRoots_on_ray hT t ν a a.2.1.2
  intro β hβ hpos
  have hβG := relativeRoots_subset_of_factor hz t ht hβ
  have hβζ := relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer
    hz t ht ζ le_rfl hβ
  exact positiveRoot_eq_pos_nsmul_of_dependent i P hP ν hT hν a ⟨hβG, hpos⟩
    (hζ a a.2.1.1 β hβG haζ hβζ)

include hP hT hν hζ haζ hz ht in
/-- The opposite chamber factor in the same Levi is the full intrinsic root
functor for the negative simple root, without reducedness assumptions. -/
theorem rankOne_unipotent_eq_negativeRoot :
    Dynamic.unipotent (CommGroupScheme.groupHom (-ν) ≫ t) =
      RelativeRoot.subgroup t (-(a : characterLattice T)) := by
  apply unipotent_eq_root_of_positiveRoots_on_ray hT t (-ν) (-(a : characterLattice T))
  · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using a.2.1.2
  · intro β hβ hpos
    have hβG := relativeRoots_subset_of_factor hz t ht hβ
    have hβζ := relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer
      hz t ht ζ le_rfl hβ
    have hnegG : -β ∈ roots i := by
      rw [← hP.2.1]
      apply P.neg_mem_range_root_iff.mpr
      rwa [hP.2.1]
    have hnegpos : 0 < latticePairing T (-β) ν := by
      simpa only [map_neg, LinearMap.neg_apply] using hpos
    have hnegζ : latticePairing T (-β) ζ = 0 := by
      simp only [map_neg, LinearMap.neg_apply, hβζ, neg_zero]
    obtain ⟨n, hn, heq⟩ := positiveRoot_eq_pos_nsmul_of_dependent i P hP ν hT hν a
      ⟨hnegG, hnegpos⟩ (hζ a a.2.1.1 (-β) hnegG haζ hnegζ)
    exact ⟨n, hn, by simpa only [smul_neg, neg_neg] using congrArg Neg.neg heq⟩

end RootFactors

section SimpleGraph

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph

/-- The actual local root factors and a representative of the intervening
chamber centralizer in the same local Levi. -/
structure RankOneRootCell (a : D.SimpleIndex) where
  middle : GroupScheme (Spec (CommRingCat.of k))
  middleHom : middle ⟶ (D.comparisons a).left
  middleClosed : IsClosedSubgroup middleHom
  middleRep : (Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫
    (D.comparisons a).leftTorus)).IsRepresentedBy middleHom
  negativeRep : (Dynamic.unipotent (CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
    (CommGroupScheme.groupHom D.directions.chamber ≫
      (D.comparisons a).leftTorus))).IsRepresentedBy (D.negativeRoot a).leftInclusion
  positiveRep : (Dynamic.unipotent (CommGroupScheme.groupHom D.directions.chamber ≫
    (D.comparisons a).leftTorus)).IsRepresentedBy (D.positiveRoot a).leftInclusion

variable [ConnectedSpace G₁.X.left]
    {J₁ : Type v}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁)

include hP₁ in
/-- The constructed positive root group represents the whole positive dynamic
factor of its actual local Levi for the common chamber. -/
theorem local_positive_rep (a : D.SimpleIndex) :
    (Dynamic.unipotent (CommGroupScheme.groupHom D.directions.chamber ≫
      (D.comparisons a).leftTorus)).IsRepresentedBy (D.positiveRoot a).leftInclusion := by
  rw [rankOne_unipotent_eq_positiveRoot i₁ P₁ hP₁ D.directions.chamber
    D.split D.directions.generic (D.directions.direction a) (D.directions.rankOne a)
    a (D.directions.annihilates a) (D.comparisons a).leftInclusion
    (D.comparisons a).leftRep (D.comparisons a).leftTorus (D.comparisons a).leftTorusComp]
  exact (D.positiveRoot a).leftRep

include hP₁ in
/-- The constructed negative root group represents the whole opposite dynamic
factor of that same local Levi. -/
theorem local_negative_rep (a : D.SimpleIndex) :
    (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      (CommGroupScheme.groupHom D.directions.chamber ≫
        (D.comparisons a).leftTorus))).IsRepresentedBy (D.negativeRoot a).leftInclusion := by
  have hneg : Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ D.directions.chamber =
      -D.directions.chamber := by
    simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
  rw [← Category.assoc]
  change (Dynamic.unipotent (CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1) ≫ D.directions.chamber) ≫
      (D.comparisons a).leftTorus)).IsRepresentedBy _
  rw [hneg, rankOne_unipotent_eq_negativeRoot i₁ P₁ hP₁ D.directions.chamber
    D.split D.directions.generic (D.directions.direction a) (D.directions.rankOne a)
    a (D.directions.annihilates a) (D.comparisons a).leftInclusion
    (D.comparisons a).leftRep (D.comparisons a).leftTorus (D.comparisons a).leftTorusComp]
  exact (D.negativeRoot a).leftRep

/-- Construct the actual local three-factor cell, using a canonical affine
representative for its middle dynamic centralizer. -/
def rankOneRootCell (a : D.SimpleIndex) : D.RankOneRootCell a := by
  let χ := CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus
  let : IsAffine (D.comparisons a).left.X.left :=
    isAffine_of_isAffineHom (D.comparisons a).left.X.hom
  exact
    { middle := Dynamic.Affine.centralizerScheme χ
      middleHom := Dynamic.Affine.centralizerHom χ
      middleClosed := Dynamic.Affine.isClosedSubgroup_centralizerHom χ
      middleRep := Dynamic.Affine.isRepresentedBy_centralizerHom χ
      negativeRep := D.local_negative_rep P₁ hP₁ a
      positiveRep := D.local_positive_rep P₁ hP₁ a }

namespace RankOneRootCell

variable {D} {a : D.SimpleIndex} (E : D.RankOneRootCell a)

omit [ConnectedSpace G₁.X.left] in
/-- The three root-cell factors multiply by an open immersion in the actual
local Levi, for every field. -/
theorem isOpenImmersion_cell :
    IsOpenImmersion (Dynamic.tripleCellMultiplication (D.negativeRoot a).leftInclusion
      E.middleHom (D.positiveRoot a).leftInclusion).left :=
  Dynamic.isOpenImmersion_tripleCellMultiplication
    (CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus)
    E.negativeRep E.middleRep E.positiveRep

/-- The open local root cell has dense image. -/
theorem isDominant_cell :
    IsDominant (Dynamic.tripleCellMultiplication (D.negativeRoot a).leftInclusion
      E.middleHom (D.positiveRoot a).leftInclusion).left :=
  Dynamic.isDominant_tripleCellMultiplication
    (CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus)
    E.negativeRep E.middleRep E.positiveRep

/-- Over an algebraically closed field, rational three-factor products are
dense in the local Levi, with the actual intrinsic root groups as end factors. -/
theorem rationalPointClosure_cell_eq_univ [IsAlgClosed k] :
    rationalPointClosure (D.comparisons a).left
      (rationalTripleProduct (D.negativeRoot a).leftInclusion E.middleHom
        (D.positiveRoot a).leftInclusion) = Set.univ :=
  rationalPointClosure_dynamicTripleProduct_eq_univ
    (CommGroupScheme.groupHom D.directions.chamber ≫ (D.comparisons a).leftTorus)
    E.negativeRep E.middleRep E.positiveRep

end RankOneRootCell
end SimpleComparisonGraph
end SimpleGraph

end Langlands.GroupScheme.LeviGluing
