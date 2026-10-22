import Langlands.Cohomology.Tate.TowerReindex
import Langlands.Cohomology.Tate.ReindexNaturality
import Langlands.Cohomology.Tate.SplitTransfer

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]
variable {K H : Subgroup G} (h : K ≤ H)

variable [Fintype G] [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)]

omit [Fintype G] [Fintype H] in
/-- Connecting compatibility for the canonical subgroup identification. -/
lemma towerReindex_delta (S : ShortComplex (Rep.{u} R G)) (hS : S.ShortExact)
    (n : ℤ) (x : tateCohomology (Rep.res K.subtype S.X₃) n) :
    (towerReindex h S.X₁ (n + 1)).hom
        (TateCohomology.δ (hS.map_of_exact (Rep.resFunctor K.subtype)) n x) =
      TateCohomology.δ
        ((hS.map_of_exact (Rep.resFunctor H.subtype)).map_of_exact
          (Rep.resFunctor (K.subgroupOf H).subtype)) n
        ((towerReindex h S.X₃ n).hom x) :=
  ConcreteCategory.congr_hom
    (reindex_delta (Subgroup.subgroupOfEquivOfLe h).symm
      (hS.map_of_exact (Rep.resFunctor K.subtype))
      ((hS.map_of_exact (Rep.resFunctor H.subtype)).map_of_exact
        (Rep.resFunctor (K.subgroupOf H).subtype))
      (towerSequenceMap h S) n) x

/-- An actual scalar splitting is unchanged by subgroup restriction. -/
def scalarSplitting_restrict (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    ((S.map (Rep.resFunctor H.subtype)).map
      (forget₂ (Rep.{u} R H) (ModuleCat.{u} R))).Splitting :=
  s

omit [Fintype G] [Fintype K] [Fintype H] in
/-- Coinduced replacements remain Tate-acyclic through both restrictions. -/
lemma towerCoinduced_tate_isZero (A : Rep.{u} R G) (n : ℤ) :
    IsZero (tateCohomology
      (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype (coinduced A))) n) :=
  (restrictedCoinduced_tate_isZero (K.subgroupOf H) (cosetCoefficients H A) n).of_iso
    ((tateCohomologyFunctor n).mapIso
      ((Rep.resFunctor (K.subgroupOf H).subtype).mapIso (restrictedCoinducedIso H A)))

/-- The actual augmentation connecting map remains invertible through the subgroup tower. -/
def towerShiftDownIso (A : Rep.{u} R G) (n : ℤ) :
    tateCohomology (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A)) n ≅
      tateCohomology
        (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype (shiftDown A))) (n + 1) := by
  let hS := ((shiftDownSequence_shortExact A).map_of_exact
    (Rep.resFunctor H.subtype)).map_of_exact (Rep.resFunctor (K.subgroupOf H).subtype)
  have := tate_delta_isIso hS n
    (towerCoinduced_tate_isZero (K := K) (H := H) A n)
    (towerCoinduced_tate_isZero (K := K) (H := H) A (n + 1))
  exact asIso (TateCohomology.δ hS n)

omit [Fintype G] [Fintype H] in
lemma towerReindex_zeroClass (A : Rep.{u} R G)
    (a : (Rep.res K.subtype A).ρ.invariants) :
    (towerReindex h A 0).hom (zeroClass (Rep.res K.subtype A) a) =
      zeroClass (Rep.res (K.subgroupOf H).subtype (Rep.res H.subtype A))
        (reindexInvariants (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom a) :=
  reindex_zeroClass (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom a

variable [Fintype (G ⧸ K)] [Fintype (G ⧸ H)] [Fintype (H ⧸ K.subgroupOf H)]

omit [Fintype G] [Fintype K] [Fintype H] [Fintype (K.subgroupOf H)] in
/-- The coset norm factors through the two levels of a subgroup tower. -/
lemma cosetNorm_trans (A : Rep.{u} R G) (a : (Rep.res K.subtype A).ρ.invariants) :
    cosetNorm K A a =
      cosetNorm H A (cosetNorm (K.subgroupOf H) (Rep.res H.subtype A)
        (reindexInvariants (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom a)) := by
  apply Subtype.ext
  change (∑ q : G ⧸ K, cosetAction K A a q) =
    ∑ q : G ⧸ H, cosetAction H A
      (cosetNorm (K.subgroupOf H) (Rep.res H.subtype A)
        (reindexInvariants (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom a)) q
  rw [← Equiv.sum_comp (Subgroup.quotientEquivProdOfLE h).symm (cosetAction K A a),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [cosetAction_out]
  change (∑ r : H ⧸ K.subgroupOf H, cosetAction K A a
      ((Subgroup.quotientEquivProdOfLE h).symm (q, r))) =
    A.ρ q.out (∑ r : H ⧸ K.subgroupOf H,
      cosetAction (K.subgroupOf H) (Rep.res H.subtype A)
        (reindexInvariants (Subgroup.subgroupOfEquivOfLe h).symm (towerCoefficientIso h A).hom a) r)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  induction r using QuotientGroup.induction_on with
  | H k =>
    change A.ρ (q.out * (k : G)) a = A.ρ q.out (A.ρ k a)
    simp only [map_mul, Module.End.mul_apply]

lemma restrictionZero_trans (A : Rep.{u} R G) (x : tateCohomology A 0) :
    (towerReindex h A 0).hom (restrictionZero K A x) =
      restrictionZero (K.subgroupOf H) (Rep.res H.subtype A) (restrictionZero H A x) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective A x
  rw [restrictionZero_zeroClass, towerReindex_zeroClass,
    restrictionZero_zeroClass, restrictionZero_zeroClass]
  rfl

lemma corestrictionZero_trans (A : Rep.{u} R G)
    (x : tateCohomology (Rep.res K.subtype A) 0) :
    corestrictionZero K A x =
      corestrictionZero H A (corestrictionZero (K.subgroupOf H) (Rep.res H.subtype A)
        ((towerReindex h A 0).hom x)) := by
  obtain ⟨a, rfl⟩ := zeroClass_surjective (Rep.res K.subtype A) x
  rw [corestrictionZero_zeroClass, towerReindex_zeroClass,
    corestrictionZero_zeroClass, corestrictionZero_zeroClass, cosetNorm_trans h]

end Langlands.Tate
