import Langlands.Representation.LanglandsClassification.ParabolicChamberBasis
import Langlands.Representation.LanglandsClassification.ParabolicChamberStatements
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped Pointwise

namespace Langlands.GroupScheme

open RealTorusSpace Module

namespace ParabolicChamberAux

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  {D : RelativeRootReflectionData i}

/-- Fundamental weights and simple coroots are biorthogonal. -/
theorem weight_pair [DecidableEq (simpleRelativeRoots i ν)]
    {α : simpleRelativeRoots i ν} {x : Vstar T}
    (hx : D.IsRealFundamentalWeight ν α x) (β : simpleRelativeRoots i ν) :
    pair T x (D.realCoroot (simpleToRelativeRoot i ν β)) = if α = β then 1 else 0 := by
  split_ifs with h
  · subst h; exact hx.2.1
  · exact hx.2.2 β (Ne.symm h)

omit [Mono i.hom.hom.left] in
/-- Fundamental coweights and simple roots are biorthogonal. -/
theorem coweight_eval [DecidableEq (simpleRelativeRoots i ν)]
    {α : simpleRelativeRoots i ν} {v : V T}
    (hv : IsRealFundamentalCoweight i ν α v) (β : simpleRelativeRoots i ν) :
    eval T β.1 v = if α = β then 1 else 0 := by
  split_ifs with h
  · subst h; exact hv.2.1
  · exact hv.2.2 β (Ne.symm h)

/-- Fundamental weights restrict to a basis of the parabolic root subspace. -/
theorem parabolic_weight_basis
    (w : Basis (simpleRelativeRoots i ν) ℝ (relativeRootSpanReal i))
    (hw : ∀ α, D.IsRealFundamentalWeight ν α (w α))
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ b : Basis {α : simpleRelativeRoots i ν // α.1 ∉ J} ℝ
        (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)),
      ∀ α, D.IsRealFundamentalWeight ν α.1 (b α) := by
  classical
  let q : simpleRelativeRoots i ν → (relativeRootSpanReal i) →ₗ[ℝ] ℝ :=
    fun α => ((pair T).flip (D.realCoroot (simpleToRelativeRoot i ν α))).comp
      (relativeRootSpanReal i).subtype
  have hq (α β : simpleRelativeRoots i ν) : q α (w β) = if β = α then 1 else 0 :=
    weight_pair (hw β) α
  obtain ⟨b, hb⟩ := restrict_submodule_basis inf_le_right w
    {α : simpleRelativeRoots i ν | α.1 ∉ J}
    (fun α hα => parabolicFundamentalWeights_subset hJ ⟨α, hα, hw α⟩) (by
      intro x α hα
      rw [repr_eq w q hq]
      exact (mem_corootAnnihilator i D J x).mp x.2.1
        (simpleToRelativeRoot i ν α) (not_not.mp hα))
  exact ⟨b, fun α => by rw [hb]; exact hw α.1⟩

omit [Mono i.hom.hom.left] in
/-- Fundamental coweights restrict to a basis of the dual parabolic subspace. -/
theorem parabolic_coweight_basis
    (w : Basis (simpleRelativeRoots i ν) ℝ
      (cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))))
    (hw : ∀ α, IsRealFundamentalCoweight i ν α (w α))
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) :
    ∃ b : Basis {α : simpleRelativeRoots i ν // α.1 ∉ J} ℝ
        (rootAnnihilator T J ⊓
          cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) :
          Submodule ℝ (V T)),
      ∀ α, IsRealFundamentalCoweight i ν α.1 (b α) := by
  classical
  let X := cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))
  let q : simpleRelativeRoots i ν → X →ₗ[ℝ] ℝ := fun α => (eval T α.1).comp X.subtype
  have hq (α β : simpleRelativeRoots i ν) : q α (w β) = if β = α then 1 else 0 :=
    coweight_eval (hw β) α
  obtain ⟨b, hb⟩ := restrict_submodule_basis inf_le_right w
    {α : simpleRelativeRoots i ν | α.1 ∉ J}
    (fun α hα => parabolicFundamentalCoweights_subset hJ ⟨α, hα, hw α⟩) (by
      intro x α hα
      rw [repr_eq w q hq]
      exact (mem_rootAnnihilator J x).mp x.2.1 α.1 (not_not.mp hα))
  exact ⟨b, fun α => by rw [hb]; exact hw α.1⟩

/-- Conditions on all complementary simple coroots are coefficient conditions. -/
theorem face_coordinate_set {J : Set (characterLattice T)}
    [Finite {α : simpleRelativeRoots i ν // α.1 ∉ J}]
    (b : Basis {α : simpleRelativeRoots i ν // α.1 ∉ J} ℝ
      (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)))
    (hb : ∀ α, D.IsRealFundamentalWeight ν α.1 (b α)) (p : ℝ → Prop) :
    {y : Vstar T | y ∈ relativeRootSpanReal i ∧
      (∀ α : relativeRoots i, α.1 ∈ J → pair T y (D.realCoroot α) = 0) ∧
      ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
        p (pair T y (D.realCoroot α))} =
      {y : Vstar T | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ,
        (∀ α, p (c α)) ∧ y = ∑ᶠ α, c α • (b α : Vstar T)} := by
  classical
  let q : {α : simpleRelativeRoots i ν // α.1 ∉ J} → Vstar T →ₗ[ℝ] ℝ :=
    fun α => (pair T).flip (D.realCoroot (simpleToRelativeRoot i ν α.1))
  have hq (α β : {α : simpleRelativeRoots i ν // α.1 ∉ J}) :
      q α (b β) = if β = α then 1 else 0 := by
    simpa only [q, LinearMap.flip_apply, Subtype.val_inj] using weight_pair (hb β) α.1
  rw [← coordinate_set b q hq p]
  ext y
  constructor
  · rintro ⟨hy, hz, hp⟩
    exact ⟨⟨(mem_corootAnnihilator i D J y).mpr hz, hy⟩,
      fun α => hp (simpleToRelativeRoot i ν α.1) α.1.2 α.2⟩
  · rintro ⟨hy, hp⟩
    refine ⟨hy.2, (mem_corootAnnihilator i D J y).mp hy.1, ?_⟩
    intro α hα hαJ
    exact hp ⟨⟨α.1, hα⟩, hαJ⟩

/-- Every root and coroot has a unique projection along complementary subspaces. -/
theorem projections_exist_unique {J : Set (characterLattice T)}
    (hroot : IsCompl (corootAnnihilator i D J)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)))
    (hcoroot : IsCompl (rootAnnihilator T J) (Submodule.span ℝ (D.realCorootsOf J)))
    (α : relativeRoots i) :
    (∃! y, y ∈ D.projectedRoots J {α.1}) ∧
      ∃! v, v ∈ D.projectedCoroots J {α.1} := by
  constructor
  · simpa only [RelativeRootReflectionData.projectedRoots, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, exists_eq_left] using
      projection_unique hroot ((1 : ℝ) ⊗ₜ[ℤ] α.1)
  · obtain ⟨v, hv, huniq⟩ := projection_unique hcoroot (D.realCoroot α)
    refine ⟨v, ⟨hv.1, D.realCoroot α, ⟨α, Set.mem_singleton _, rfl⟩, hv.2⟩, ?_⟩
    rintro v' ⟨hv', _, ⟨β, hβ, rfl⟩, hdiff⟩
    have hβα : β = α := Subtype.ext (Set.mem_singleton_iff.mp hβ)
    exact huniq v' ⟨hv', hβα ▸ hdiff⟩

/-- Fundamental coweights separate the projected complementary simple roots. -/
theorem projected_roots_distinct
    (w : Basis (simpleRelativeRoots i ν) ℝ
      (cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))))
    (hw : ∀ α, IsRealFundamentalCoweight i ν α (w α))
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {α α' : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν \ J)
    (hα' : α' ∈ simpleRelativeRoots i ν \ J) {y : Vstar T}
    (hy : y ∈ D.projectedRoots J {α}) (hy' : y ∈ D.projectedRoots J {α'}) : α = α' := by
  by_contra hne
  let a : simpleRelativeRoots i ν := ⟨α, hα.1⟩
  have hmem := parabolicFundamentalCoweights_subset hJ ⟨a, hα.2, hw a⟩
  have h1 := pair_eq_of_mem_projectedRoots hmem.1 α hy
  have h0 := pair_eq_of_mem_projectedRoots hmem.1 α' hy'
  rw [(hw a).2.1] at h1
  have hother := (hw a).2.2 ⟨α', hα'.1⟩ (fun h => hne (congrArg Subtype.val h).symm)
  rw [hother] at h0
  linarith

/-- The chamber conditions may be tested on projected simple coroots. -/
theorem chamber_projected_set {J : Set (characterLattice T)}
    (hproj : ∀ α ∈ simpleRelativeRoots i ν \ J,
      (∃ y, y ∈ D.projectedRoots J {α}) ∧ ∃ v, v ∈ D.projectedCoroots J {α})
    (p : ℝ → Prop) :
    {y : Vstar T | (∀ α : relativeRoots i, α.1 ∈ J →
        pair T y (D.realCoroot α) = 0) ∧
      ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
        p (pair T y (D.realCoroot α))} =
      {y : Vstar T | y ∈ corootAnnihilator i D J ∧
        ∀ y' v, IsParabolicCorootOf i ν D J y' v → p (pair T y v)} := by
  ext y
  constructor
  · rintro ⟨hz, hp⟩
    have hy := (mem_corootAnnihilator i D J y).mpr hz
    refine ⟨hy, ?_⟩
    rintro y' v ⟨α, hα, -, hv⟩
    rw [pair_eq_of_mem_projectedCoroots hy
      ⟨α, simpleRelativeRoots_subset_relativeRoots i ν hα.1⟩ hv]
    exact hp _ hα.1 hα.2
  · rintro ⟨hy, hp⟩
    refine ⟨(mem_corootAnnihilator i D J y).mp hy, ?_⟩
    intro α hα hαJ
    obtain ⟨⟨y', hy'⟩, v, hv⟩ := hproj α.1 ⟨hα, hαJ⟩
    have h := hp y' v ⟨α.1, ⟨hα, hαJ⟩, hy', hv⟩
    rwa [pair_eq_of_mem_projectedCoroots hy α hv] at h

/-- Central characters do not change the simple-coroot conditions, and the
character/root complement separates the central part of a chamber. -/
theorem chamber_central_set
    (hcomp : IsCompl (relativeRootSpanReal i)
      (LinearMap.range (rationalCharacterRestrictReal i)))
    (hcent : corootAnnihilator i D (simpleRelativeRoots i ν) =
      LinearMap.range (rationalCharacterRestrictReal i))
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) (p : ℝ → Prop) :
    {y : Vstar T | (∀ α : relativeRoots i, α.1 ∈ J →
        pair T y (D.realCoroot α) = 0) ∧
      ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
        p (pair T y (D.realCoroot α))} =
      {y : Vstar T | y ∈ relativeRootSpanReal i ∧
        (∀ α : relativeRoots i, α.1 ∈ J → pair T y (D.realCoroot α) = 0) ∧
        ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
          p (pair T y (D.realCoroot α))} +
        (LinearMap.range (rationalCharacterRestrictReal i) : Set (Vstar T)) := by
  have hpair (x μ : Vstar T) (hμ : μ ∈ LinearMap.range (rationalCharacterRestrictReal i))
      (α : relativeRoots i) (hα : α.1 ∈ simpleRelativeRoots i ν) :
      pair T (x + μ) (D.realCoroot α) = pair T x (D.realCoroot α) := by
    have hz := (mem_corootAnnihilator i D (simpleRelativeRoots i ν) μ).mp
      (hcent ▸ hμ) α hα
    change pair T μ (D.realCoroot α) = 0 at hz
    rw [map_add, LinearMap.add_apply, hz, add_zero]
  ext y
  constructor
  · intro hy
    obtain ⟨x, μ, hadd, -⟩ := Submodule.existsUnique_add_of_isCompl hcomp y
    refine Set.mem_add.mpr ⟨x, ⟨x.2, ?_, ?_⟩, μ, μ.2, hadd⟩
    · intro α hα
      have hz := hy.1 α hα
      rwa [← hadd, hpair _ _ μ.2 α (hJ hα)] at hz
    · intro α hα hαJ
      have hp := hy.2 α hα hαJ
      rwa [← hadd, hpair _ _ μ.2 α hα] at hp
  · rintro ⟨x, hx, μ, hμ, rfl⟩
    refine ⟨fun α hα => ?_, fun α hα hαJ => ?_⟩
    · rw [hpair x μ hμ α (hJ hα)]
      exact hx.2.1 α hα
    · rw [hpair x μ hμ α hα]
      exact hx.2.2 α hα hαJ

end ParabolicChamberAux

/-- The chamber theorem follows from the fundamental bases and the standard-Levi
real decompositions. -/
theorem parabolicChamberLinearAlgebra_of_statements
    (hfund : RelativeFundamentalWeightStatement.{u})
    (hlevi : StandardLeviRealDecompositionStatement.{u}) :
    ParabolicChamberLinearAlgebraStatement.{u} := by
  classical
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let := hi.isSplitSubtorus.1.finite_realCharacterSpace
  intro ν hν D J hJ
  have hf := hfund k G hG T i hi ν hν D
  have hl := hlevi k G hG T i hi ν hν D
  have hlj := hl.2.2.2 J J Set.Subset.rfl hJ
  obtain ⟨w, hw⟩ := hf.2.1
  obtain ⟨cw, hcw⟩ := hf.2.2.1
  let := FiniteDimensional.fintypeBasisIndex w
  obtain ⟨b, hb⟩ := ParabolicChamberAux.parabolic_weight_basis w hw hJ
  obtain ⟨c, hc⟩ := ParabolicChamberAux.parabolic_coweight_basis cw hcw hJ
  have hproj : ∀ α ∈ simpleRelativeRoots i ν \ J,
      (∃! y, y ∈ D.projectedRoots J {α}) ∧ ∃! v, v ∈ D.projectedCoroots J {α} := by
    intro α hα
    exact ParabolicChamberAux.projections_exist_unique hlj.1 hlj.2.1
      ⟨α, simpleRelativeRoots_subset_relativeRoots i ν hα.1⟩
  have hopen : openCorootFace i ν D J =
      {y | ∃ d : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ,
        (∀ α, 0 < d α) ∧ y = ∑ᶠ α, d α • (b α : Vstar T)} :=
    ParabolicChamberAux.face_coordinate_set b hb (fun r => 0 < r)
  have hclosed : closedCorootFace i ν D J =
      {y | ∃ d : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ,
        (∀ α, 0 ≤ d α) ∧ y = ∑ᶠ α, d α • (b α : Vstar T)} :=
    ParabolicChamberAux.face_coordinate_set b hb (fun r => 0 ≤ r)
  have hcomp := (relativeCharacterRootComplement k G hG T i hi).2
  have hopen_sum : openSimpleCorootFace i ν D J = openCorootFace i ν D J +
      (LinearMap.range (rationalCharacterRestrictReal i) : Set (Vstar T)) :=
    ParabolicChamberAux.chamber_central_set hcomp hl.1 hJ (fun r => 0 < r)
  have hclosed_sum : closedSimpleCorootFace i ν D J = closedCorootFace i ν D J +
      (LinearMap.range (rationalCharacterRestrictReal i) : Set (Vstar T)) :=
    ParabolicChamberAux.chamber_central_set hcomp hl.1 hJ (fun r => 0 ≤ r)
  have hproj' : ∀ α ∈ simpleRelativeRoots i ν \ J,
      (∃ y, y ∈ D.projectedRoots J {α}) ∧ ∃ v, v ∈ D.projectedCoroots J {α} :=
    fun α hα => ⟨(hproj α hα).1.exists, (hproj α hα).2.exists⟩
  refine ⟨hproj, ?_, ⟨b, hb, hopen, hclosed, ?_, ?_⟩, ⟨c, hc⟩,
    ?_, ?_, hopen_sum, hclosed_sum, ?_⟩
  · intro α hα α' hα' y hy hy'
    exact ParabolicChamberAux.projected_roots_distinct cw hcw hJ hα hα' hy hy'
  · rw [hopen_sum, hopen]
    exact ParabolicChamberAux.coefficient_set_add _ _ _
  · rw [hclosed_sum, hclosed]
    exact ParabolicChamberAux.coefficient_set_add _ _ _
  · exact ParabolicChamberAux.chamber_projected_set hproj' (fun r => 0 < r)
  · exact ParabolicChamberAux.chamber_projected_set hproj' (fun r => 0 ≤ r)
  · let : TopologicalSpace (Vstar T) := moduleTopology ℝ (Vstar T)
    let : T2Space (Vstar T) := ParabolicChamberAux.moduleTopology_t2
    let := IsModuleTopology.isTopologicalAddGroup ℝ (Vstar T)
    rw [hopen, hclosed]
    exact ParabolicChamberAux.orthant_topology _ b

/-- Parabolic chamber projections, fundamental bases, inequalities and topology. -/
theorem parabolicChamberLinearAlgebra : ParabolicChamberLinearAlgebraStatement.{u} :=
  parabolicChamberLinearAlgebra_of_statements
    relativeFundamentalWeight standardLeviRealDecomposition

end Langlands.GroupScheme
