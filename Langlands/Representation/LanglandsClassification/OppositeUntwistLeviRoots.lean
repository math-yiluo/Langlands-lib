import Langlands.Representation.LanglandsClassification.OppositeStandardNesting
import Langlands.Representation.LanglandsClassification.StandardParabolicRootPresentation
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction
import Langlands.Representation.Aubert.General.RationalOppositeChamber

/-! # Standard parabolics of a standard Levi for the negated cocharacter

For a generic cocharacter `ν`, the relative roots positive (respectively
simple) for `-ν` are the negatives of those positive (respectively simple)
for `ν`. Inside the standard Levi `M_K`, with the ambient maximal split torus,
the standard parabolics for `-ν` are cut out by the opposite standard
parabolics `P̄_J` of the labels `J ⊆ K`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

section Negation

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

theorem latticePairing_neg_cocharacter (α : characterLattice T) (ζ : cocharacterLattice T) :
    latticePairing T α (-ζ) = latticePairing T (-α) ζ := by
  simp only [map_neg, LinearMap.neg_apply]

variable {i}

/-- The roots positive for `-ν` are the negatives of the roots positive for `ν`. -/
theorem mem_positiveRelativeRoots_neg
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) {α : characterLattice T} :
    α ∈ positiveRelativeRoots i (-ν) ↔ -α ∈ positiveRelativeRoots i ν := by
  have hroot : α ∈ relativeRoots i ↔ -α ∈ relativeRoots i :=
    ⟨hneg α, fun h => by simpa using hneg (-α) h⟩
  simp only [positiveRelativeRoots, Set.mem_ofPred_eq, latticePairing_neg_cocharacter, hroot]

/-- The roots simple for `-ν` are the negatives of the roots simple for `ν`. -/
theorem mem_simpleRelativeRoots_neg
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) {α : characterLattice T} :
    α ∈ simpleRelativeRoots i (-ν) ↔ -α ∈ simpleRelativeRoots i ν := by
  simp only [simpleRelativeRoots, Set.mem_ofPred_eq, mem_positiveRelativeRoots_neg ν hneg]
  refine and_congr Iff.rfl (not_congr ⟨?_, ?_⟩)
  · rintro ⟨b, hb, c, hc, rfl⟩
    exact ⟨-b, hb, -c, hc, by abel⟩
  · rintro ⟨b, hb, c, hc, h⟩
    refine ⟨-b, by simpa using hb, -c, by simpa using hc, ?_⟩
    rw [← neg_neg α, h, neg_add]

/-- Negating both the cocharacter and the index gives a standard cocharacter for `-ν`. -/
theorem IsStandardCocharacter.negIndexSet
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν J ζ) :
    IsStandardCocharacter i (-ν) (-J) (-ζ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    exact (mem_simpleRelativeRoots_neg ν hneg).mpr (hζ.1 (Set.mem_neg.mp hα))
  · intro α hα
    rw [latticePairing_neg_cocharacter]
    exact hζ.2.1 _ (Set.mem_neg.mp hα)
  · intro α hα hαJ
    rw [latticePairing_neg_cocharacter]
    exact hζ.2.2 _ ((mem_simpleRelativeRoots_neg ν hneg).mp hα)
      (fun h => hαJ (Set.mem_neg.mpr h))

theorem neg_subset_simpleRelativeRoots_neg
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    -J ⊆ simpleRelativeRoots i (-ν) :=
  fun _ hα => (mem_simpleRelativeRoots_neg ν hneg).mpr (hJ (Set.mem_neg.mp hα))

end Negation

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily.Nesting

open GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi in
theorem relativeRoots_neg_mem : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i :=
  relativeRootNegation k G hG T i hi

include hG hi hν in
/-- A standard Levi for `ν` is the standard Levi for `-ν` of the negated label. -/
theorem standardLevi_neg {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardLevi i (-ν) (-J) = standardLevi i ν J := by
  have := hi.isSplitSubtorus.mono
  have hneg := relativeRoots_neg_mem i hG hi
  obtain ⟨⟨eta0, heta⟩, hcmp⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  have heta' := heta.negIndexSet ν hneg
  obtain ⟨-, hcmp'⟩ := standardCocharacter k G hG T i hi (-ν) (hν.neg i ν) (-J) heta'.1
  rw [(hcmp' _ heta').2.1, (hcmp eta0 heta).2.1, groupHom_neg_comp_eq_oppositeCocharacter,
    Dynamic.centralizer_oppositeCocharacter]

include hG hi hν in
/-- The standard parabolic for `-ν` of the negated label is the chosen opposite
of the standard parabolic of the label. -/
theorem standardParabolic_neg (J : StandardJacquetFamily.Index i ν) :
    standardParabolic i (-ν) (-J.val) =
      SubgroupFunctor.range (OppositeStandardJacquetFamily.datum i ν hG hi hν J).p := by
  have := hi.isSplitSubtorus.mono
  have hneg := relativeRoots_neg_mem i hG hi
  obtain ⟨⟨eta0, heta⟩, hcmp⟩ := standardCocharacter k G hG T i hi ν hν J.val J.property
  have heta' := heta.negIndexSet ν hneg
  obtain ⟨-, hcmp'⟩ := standardCocharacter k G hG T i hi (-ν) (hν.neg i ν) (-J.val) heta'.1
  rw [(hcmp' _ heta').1, range_opposite_p_eq]
  have heq : Dynamic.parabolic (CommGroupScheme.groupHom eta0 ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom (lattice i ν hG hi hν J) ≫ i) := by
    rw [← (hcmp eta0 heta).1, lattice_comp, standardParabolic_eq_realizing]
  exact le_antisymm (parabolic_neg_le_neg i hG hi heq.le)
    (parabolic_neg_le_neg i hG hi heq.ge)

/-! ### Inside the standard Levi of a label `K` -/

variable (K : StandardJacquetFamily.Index i ν)

/-- The ambient maximal split torus, factored through the standard Levi of `K`. -/
abbrev leviTorus : T.toGrp ⟶ Standard.leviScheme i ν K.val :=
  standardLeviTorusFactor i ν K.val (Standard.isRepresentedBy_leviHom i ν K.val)

theorem leviTorus_comp :
    leviTorus i ν K ≫ Standard.leviHom i ν K.val = i :=
  standardLeviTorusFactor_comp _ _ _ _

include hG hi hν in
theorem isRepresentedBy_leviHom_neg :
    (standardLevi i (-ν) (-K.val)).IsRepresentedBy (Standard.leviHom i ν K.val) := by
  rw [standardLevi_neg i ν hG hi hν K.property]
  exact Standard.isRepresentedBy_leviHom i ν K.val

include hG hi hν in
theorem standardLeviTorusFactor_neg :
    standardLeviTorusFactor i (-ν) (-K.val) (isRepresentedBy_leviHom_neg i ν hG hi hν K) =
      leviTorus i ν K :=
  SubgroupFunctor.IsRepresentedBy.hom_ext (Standard.isRepresentedBy_leviHom i ν K.val)
    ((standardLeviTorusFactor_comp _ _ _ _).trans (leviTorus_comp i ν K).symm)

include hi in
theorem isMaximalSplitTorus_leviTorus : IsMaximalSplitTorus (leviTorus i ν K) :=
  hi.isMaximalSplitTorus_standardLeviTorusFactor i ν K.val _
    (Standard.isClosedSubgroup_leviHom i ν K.val)

include hG hi hν in
/-- The standard-family comparison inside `M_K`, for the negated cocharacter. -/
theorem leviTorus_neg_families :
    haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
    simpleRelativeRoots (leviTorus i ν K) (-ν) = -K.val ∧
      IsGenericCocharacter (leviTorus i ν K) (-ν) ∧
      ∀ J' : Set (characterLattice T), J' ⊆ -K.val →
        standardParabolic (leviTorus i ν K) (-ν) J' =
            (standardParabolic i (-ν) J').comap (Standard.leviHom i ν K.val) ∧
          standardLevi (leviTorus i ν K) (-ν) J' =
            (standardLevi i (-ν) J').comap (Standard.leviHom i ν K.val) := by
  have := hi.isSplitSubtorus.mono
  have hneg := relativeRoots_neg_mem i hG hi
  have h := standardLeviStandardFamilies dynamicLie standardCocharacter k G hG T i hi (-ν)
    (hν.neg i ν) (-K.val) (neg_subset_simpleRelativeRoots_neg ν hneg K.property)
    (Standard.leviScheme i ν K.val) (isConnectedReductive_levi i ν hG hi hν K)
    (Standard.leviHom i ν K.val) (isRepresentedBy_leviHom_neg i ν hG hi hν K)
    (Standard.isClosedSubgroup_leviHom i ν K.val)
  simp only [standardLeviTorusFactor_neg i ν hG hi hν K] at h
  exact ⟨h.1, h.2.1, fun J' hJ' => ⟨(h.2.2 J' hJ').1, (h.2.2 J' hJ').2.1⟩⟩

/-! ### Standard test data of `M_K` for the negated cocharacter -/

variable {K} in
/-- The negation of a label contained in `-K`, as a standard label for `ν`. -/
def negIndex {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val) :
    StandardJacquetFamily.Index i ν :=
  ⟨-J', fun α hα => by
    have h := hJ' (Set.mem_neg.mp hα)
    rw [Set.mem_neg, neg_neg] at h
    exact K.property h⟩

variable {K} in
@[simp] theorem negIndex_val {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val) :
    (negIndex i ν hJ').val = -J' := rfl

variable {K} in
theorem negIndex_subset {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val) :
    (negIndex i ν hJ').val ⊆ K.val := fun α hα => by
  have h := hJ' (Set.mem_neg.mp hα)
  rwa [Set.mem_neg, neg_neg] at h

variable {K} in
include hG hi hν in
/-- An actual parabolic of `M_K` representing the standard parabolic of `J' ⊆ -K`
for `-ν` is cut out in `G` by the chosen opposite parabolic of the label `-J'`. -/
theorem range_comp_leviHom_of_standardParabolic
    {P' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ Standard.leviScheme i ν K.val)
    {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val)
    (hP : haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
      SubgroupFunctor.range p' = standardParabolic (leviTorus i ν K) (-ν) J') :
    SubgroupFunctor.range (p' ≫ Standard.leviHom i ν K.val) =
      SubgroupFunctor.range (Standard.leviHom i ν K.val) ⊓
        SubgroupFunctor.range
          (OppositeStandardJacquetFamily.datum i ν hG hi hν (negIndex i ν hJ')).p := by
  have hfam := ((leviTorus_neg_families i ν hG hi hν K).2.2 J' hJ').1
  apply RepresentedParabolicLeviIntersection.range_comp_eq_inf_of_range_eq_comap
  rw [hP, hfam, ← standardParabolic_neg i ν hG hi hν (negIndex i ν hJ'), negIndex_val, neg_neg]

variable {K} in
include hG hi hν in
/-- The rational-point form of `range_comp_leviHom_of_standardParabolic`. -/
theorem pointImage_comp_leviHom_of_standardParabolic
    {P' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ Standard.leviScheme i ν K.val)
    {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val)
    (hP : haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
      SubgroupFunctor.range p' = standardParabolic (leviTorus i ν K) (-ν) J') :
    pointImage (p' ≫ Standard.leviHom i ν K.val) =
      pointImage (Standard.leviHom i ν K.val) ⊓
        pointImage (OppositeStandardJacquetFamily.datum i ν hG hi hν (negIndex i ν hJ')).p :=
  congrArg
    (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (range_comp_leviHom_of_standardParabolic i ν hG hi hν p' hJ' hP)

variable {K} in
/-- The canonical inclusion `M_J → M_K` represents the preimage of the standard Levi of `J`. -/
theorem isRepresentedBy_leviInclusion {J : StandardJacquetFamily.Index i ν} (h : J.val ⊆ K.val) :
    ((standardLevi i ν J.val).comap (Standard.leviHom i ν K.val)).IsRepresentedBy
      (leviInclusion i ν hG hi hν h) := by
  have hm : Mono (Standard.leviHom i ν K.val).hom.hom :=
    (Standard.isRepresentedBy_leviHom i ν K.val).1
  refine ⟨mono_leviInclusion i ν hG hi hν h, ?_⟩
  rw [← (Standard.isRepresentedBy_leviHom i ν J.val).2]
  refine SubgroupFunctor.ext fun U => Subgroup.ext fun x => ?_
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← leviInclusion_comp i ν hG hi hν h, Grp.comp_hom_hom, Category.assoc]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, (cancel_mono (Standard.leviHom i ν K.val).hom.hom).mp ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, leviInclusion_comp, hy]

variable {K} in
include hG hi hν in
/-- An actual Levi of `M_K` representing the standard Levi of `J' ⊆ -K` for `-ν`
represents the same subgroup functor as the inclusion of `M_{-J'}`. -/
theorem isRepresentedBy_comp_of_standardLevi
    {P' M' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ Standard.leviScheme i ν K.val)
    (l' : M' ⟶ P') (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val)
    (hM : haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
      SubgroupFunctor.range (l' ≫ p') = standardLevi (leviTorus i ν K) (-ν) J') :
    ((standardLevi i ν (negIndex i ν hJ').val).comap
      (Standard.leviHom i ν K.val)).IsRepresentedBy (l' ≫ p') := by
  refine ⟨?_, ?_⟩
  · have := hl'.isClosedSubgroup.mono_overHom
    have := hp'.isClosedSubgroup.mono_overHom
    rw [Grp.comp_hom_hom]
    infer_instance
  · have hfam := ((leviTorus_neg_families i ν hG hi hν K).2.2 J' hJ').2
    have hneg := standardLevi_neg i ν hG hi hν (negIndex i ν hJ').property
    rw [negIndex_val, neg_neg] at hneg
    rw [hM, hfam, hneg, negIndex_val]

variable {K} in
/-- The identification of the test Levi with the standard Levi of `-J'`. -/
def testLeviIso
    {P' M' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ Standard.leviScheme i ν K.val)
    (l' : M' ⟶ P') (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val)
    (hM : haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
      SubgroupFunctor.range (l' ≫ p') = standardLevi (leviTorus i ν K) (-ν) J') :
    M' ≅ Standard.leviScheme i ν (negIndex i ν hJ').val :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (isRepresentedBy_comp_of_standardLevi i ν hG hi hν p' l' hp' hl' hJ' hM)
    (isRepresentedBy_leviInclusion i ν hG hi hν (negIndex_subset i ν hJ'))

variable {K} in
theorem testLeviIso_hom_comp
    {P' M' : GroupScheme (Spec (CommRingCat.of k))} (p' : P' ⟶ Standard.leviScheme i ν K.val)
    (l' : M' ⟶ P') (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
    {J' : Set (characterLattice T)} (hJ' : J' ⊆ -K.val)
    (hM : haveI := (isConnectedReductive_levi i ν hG hi hν K).isAffineHom
      SubgroupFunctor.range (l' ≫ p') = standardLevi (leviTorus i ν K) (-ν) J') :
    (testLeviIso i ν hG hi hν p' l' hp' hl' hJ' hM).hom ≫
        leviInclusion i ν hG hi hν (negIndex_subset i ν hJ') = l' ≫ p' :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily.Nesting
