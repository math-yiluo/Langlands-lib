import Langlands.Representation.LanglandsClassification.SimpleCorootFaces
import Langlands.Representation.LanglandsClassification.ParabolicChamberStatements
import Langlands.GroupScheme.Rational.LanglandsCharacterRestriction

/-! # Transport from standard-Levi annihilators to a split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

section Restriction

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {D : RelativeRootReflectionData i}
  {J : Set (characterLattice T)} {f : A ⟶ T}

/-- Restriction is bijective on any complement of its known root-span kernel. -/
theorem splitComponent_restrict_bijOn
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hinj : Function.Injective (cocharacterMapReal f))
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hc : IsCompl (corootAnnihilator i D J)
      (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J))) :
    Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ := by
  have hk := ker_restrictReal_eq_rootSpan_of_range hA hT f J hrange
  have hlift := Langlands.LinearAlgebra.existsUnique_preimage_of_isCompl
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
    (restrictReal_surjective_of_cocharacterMapReal_injective hA hT f hinj)
    (corootAnnihilator i D J) (hk ▸ hc.symm)
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨z, hz, hu⟩ := hlift
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y)
    exact (hu x ⟨hx, hxy⟩).trans (hu y ⟨hy, rfl⟩).symm
  · intro x _
    obtain ⟨y, hy, -⟩ := hlift x
    exact ⟨y, hy⟩

/-- A projected root has the same restriction as the original root. -/
theorem restrict_eq_of_mem_projectedRoots
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    {α : characterLattice T} {y : Vstar T} (hy : y ∈ D.projectedRoots J {α}) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = restrictedRootVector f α := by
  obtain ⟨-, α', hα', hy⟩ := hy
  have he : α' = α := Set.mem_singleton_iff.mp hα'
  subst α'
  have hk := ker_restrictReal_eq_rootSpan_of_range hA hT f J hrange
  rw [← hk, LinearMap.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy.symm

/-- The projected and restricted simple-root sets agree under restriction. -/
theorem restrict_image_parabolicRoots
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ y, y ∈ D.projectedRoots J {α}) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) '' parabolicRoots i ν D J =
      restrictedSimpleRoots i ν J f := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyJ, α, hα, hdiff⟩ := hy
    refine ⟨α, hα, ?_⟩
    exact (restrict_eq_of_mem_projectedRoots hA hT hrange
      ⟨hyJ, α, Set.mem_singleton _, hdiff⟩).symm
  · rintro ⟨α, hα, rfl⟩
    obtain ⟨y, hy⟩ := hp α hα
    refine ⟨y, ?_, restrict_eq_of_mem_projectedRoots hA hT hrange hy⟩
    obtain ⟨hyJ, α', hα', hdiff⟩ := hy
    have he : α' = α := Set.mem_singleton_iff.mp hα'
    subst α'
    exact ⟨hyJ, α, hα, hdiff⟩

/-- The printed pair inequalities are exactly the lifted simple-coroot inequalities.
The predicate may be strict positivity, nonnegativity, or any other real condition. -/
theorem splitComponent_pairCondition_iff
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ v, v ∈ D.projectedCoroots J {α})
    (P : ℝ → Prop) (x : Vstar A) :
    (∀ β v, IsRestrictedParabolicCoroot i ν D J f β v → P (pair A x v)) ↔
      ∃ y : Vstar T, rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x ∧
        (∀ α : relativeRoots i, α.1 ∈ J → pair T y (D.realCoroot α) = 0) ∧
        ∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
          P (pair T y (D.realCoroot α)) := by
  constructor
  · intro hx
    obtain ⟨y, hyJ, hyx⟩ := hbij.surjOn (Set.mem_univ x)
    refine ⟨y, hyx, (mem_corootAnnihilator i D J y).mp hyJ, ?_⟩
    intro α hα hαJ
    obtain ⟨v, hv⟩ := hp α.1 ⟨hα, hαJ⟩
    have hvr : v ∈ (cocharacterMapReal f).range := hrange ▸ hv.1
    obtain ⟨w, rfl⟩ := hvr
    have hw := hx (restrictedRootVector f α.1) w ⟨α.1, ⟨hα, hαJ⟩, rfl, hv⟩
    rwa [← hyx, ← pair_cocharacterMapReal,
      pair_eq_of_mem_projectedCoroots hyJ α hv] at hw
  · rintro ⟨y, hyx, hyJ, hypos⟩ β w ⟨α, hα, -, hw⟩
    have hαR := simpleRelativeRoots_subset_relativeRoots i ν hα.1
    rw [← hyx, ← pair_cocharacterMapReal,
      pair_eq_of_mem_projectedCoroots ((mem_corootAnnihilator i D J y).mpr hyJ)
        ⟨α, hαR⟩ hw]
    exact hypos ⟨α, hαR⟩ hα.1 hα.2

/-- The printed chamber agrees with the existing chamber defined by lifts. -/
theorem splitComponent_openChamber_eq
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ v, v ∈ D.projectedCoroots J {α}) :
    parabolicCorootChamber i ν D J f = restrictedCorootChamber i ν J f D := by
  ext x
  exact splitComponent_pairCondition_iff hbij hrange hp (0 < ·) x

/-- The same transport for closed chambers. -/
theorem splitComponent_closedChamber_eq
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ v, v ∈ D.projectedCoroots J {α}) :
    parabolicClosedCorootChamber i ν D J f = restrictedClosedCorootChamber i ν J f D := by
  ext x
  exact splitComponent_pairCondition_iff hbij hrange hp (0 ≤ ·) x

/-- Distinct projected simple roots have distinct restrictions. -/
theorem splitComponent_root_injective
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃ y, y ∈ D.projectedRoots J {α})
    (hsep : ∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J, ∀ y,
      y ∈ D.projectedRoots J {α} → y ∈ D.projectedRoots J {α'} → α = α') :
    ∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J,
      restrictedRootVector f α = restrictedRootVector f α' → α = α' := by
  intro α hα α' hα' he
  obtain ⟨y, hy⟩ := hp α hα
  obtain ⟨y', hy'⟩ := hp α' hα'
  have hyy' := hbij.injOn hy.1 hy'.1
    ((restrict_eq_of_mem_projectedRoots hA hT hrange hy).trans
      (he.trans (restrict_eq_of_mem_projectedRoots hA hT hrange hy').symm))
  exact hsep α hα α' hα' y hy (hyy' ▸ hy')

/-- Pull the uniquely projected coroot back through the injective cocharacter map. -/
theorem splitComponent_coroot_existsUnique
    (hinj : Function.Injective (cocharacterMapReal f))
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hp : ∀ α ∈ simpleRelativeRoots i ν \ J, ∃! v, v ∈ D.projectedCoroots J {α})
    (hsep : ∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J,
      restrictedRootVector f α = restrictedRootVector f α' → α = α') :
    ∀ β ∈ restrictedSimpleRoots i ν J f, ∃! v, IsRestrictedParabolicCoroot i ν D J f β v := by
  rintro β ⟨α, hα, rfl⟩
  obtain ⟨v, hv, hu⟩ := hp α hα
  obtain ⟨w, hw⟩ := (show v ∈ (cocharacterMapReal f).range from hrange ▸ hv.1)
  refine ⟨w, ⟨α, hα, rfl, hw.symm ▸ hv⟩, ?_⟩
  rintro w' ⟨α', hα', he, hv'⟩
  have hαeq := hsep α' hα' α hα he
  subst α'
  exact hinj ((hu _ hv').trans hw.symm)

omit [Mono i.hom.hom.left] in
/-- A fundamental coweight outside `J` has a unique split-component preimage. -/
theorem splitComponent_fundamentalCoweight_existsUnique
    (hJ : J ⊆ simpleRelativeRoots i ν)
    (hinj : Function.Injective (cocharacterMapReal f))
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hex : ∀ α : simpleRelativeRoots i ν, α.1 ∉ J →
      ∃ v, IsRealFundamentalCoweight i ν α v)
    (hu : ∀ α v w, IsRealFundamentalCoweight i ν α v →
      IsRealFundamentalCoweight i ν α w → v = w) :
    ∀ α : simpleRelativeRoots i ν, α.1 ∉ J →
      ∃! w : V A, IsRealFundamentalCoweight i ν α (cocharacterMapReal f w) := by
  intro α hα
  obtain ⟨v, hv⟩ := hex α hα
  have hvJ := (parabolicFundamentalCoweights_subset hJ ⟨α, hα, hv⟩).1
  obtain ⟨w, hw⟩ := (show v ∈ (cocharacterMapReal f).range from hrange ▸ hvJ)
  refine ⟨w, ?_, fun w' hw' => hinj ?_⟩
  · change IsRealFundamentalCoweight i ν α (cocharacterMapReal f w)
    rw [hw]
    exact hv
  · exact (hu α _ v hw' hv).trans hw.symm

/-- Restriction of a fundamental-weight description allows arbitrary representatives,
because the ambient fundamental weights are unique. -/
theorem splitComponent_image_weight_description
    {C : Set (Vstar T)} (P : ℝ → Prop)
    (b : {α : simpleRelativeRoots i ν // α.1 ∉ J} → Vstar T)
    (hb : ∀ α, D.IsRealFundamentalWeight ν α.1 (b α))
    (hu : ∀ α x y, D.IsRealFundamentalWeight ν α x →
      D.IsRealFundamentalWeight ν α y → x = y)
    (hC : C = {y | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ,
      (∀ α, P (c α)) ∧ ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
        y = ∑ᶠ α, c α • b α + μ}) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) '' C =
      {x | ∃ (c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ)
          (ϖ : {α : simpleRelativeRoots i ν // α.1 ∉ J} → Vstar T),
        (∀ α, P (c α)) ∧ (∀ α, D.IsRealFundamentalWeight ν α.1 (ϖ α)) ∧
        ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
          x = rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
            (∑ᶠ α, c α • ϖ α + μ)} := by
  rw [hC]
  ext x
  constructor
  · rintro ⟨y, ⟨c, hc, μ, hμ, rfl⟩, rfl⟩
    exact ⟨c, b, hc, hb, μ, hμ, rfl⟩
  · rintro ⟨c, ϖ, hc, hϖ, μ, hμ, rfl⟩
    have he : ϖ = b := funext fun α => hu α.1 _ _ (hϖ α) (hb α)
    subst ϖ
    exact ⟨_, ⟨c, hc, μ, hμ, rfl⟩, rfl⟩

/-- The lifted closed chamber is the image of the ambient closed face. -/
theorem restrictedClosedCorootChamber_eq_image :
    restrictedClosedCorootChamber i ν J f D =
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
        closedSimpleCorootFace i ν D J := by
  ext x
  constructor
  · rintro ⟨y, hy, hz, hp⟩
    exact ⟨y, ⟨hz, hp⟩, hy⟩
  · rintro ⟨y, ⟨hz, hp⟩, hy⟩
    exact ⟨y, hy, hz, hp⟩

/-- Restriction carries the positive projected-root cone onto the restricted-root cone. -/
theorem splitComponent_image_rootPositiveCone
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hfin : (simpleRelativeRoots i ν).Finite) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
        projectedRootPositiveCone i D J (simpleRelativeRoots i ν \ J) =
      restrictedRootPositiveCone i ν J f hfin := by
  classical
  have hk := ker_restrictReal_eq_rootSpan_of_range hA hT f J hrange
  have hS : (simpleRelativeRoots i ν \ J).Finite := hfin.subset Set.sdiff_subset
  ext x
  constructor
  · rintro ⟨y, ⟨hy, s, c, hs, hc, hdiff⟩, rfl⟩
    apply (mem_restrictedRootPositiveCone_iff_roots i ν J f hfin s hs).mpr
    refine ⟨c, hc, ?_⟩
    rw [← hk, LinearMap.mem_ker, map_sub, map_sum] at hdiff
    simpa only [map_smul, restrictedRootVector] using (sub_eq_zero.mp hdiff).symm
  · intro hx
    let s := hS.toFinset
    have hs : (s : Set (characterLattice T)) = simpleRelativeRoots i ν \ J :=
      hS.coe_toFinset
    obtain ⟨c, hc, hcx⟩ :=
      (mem_restrictedRootPositiveCone_iff_roots i ν J f hfin s hs).mp hx
    obtain ⟨y, hy, hyx⟩ := hbij.surjOn (Set.mem_univ x)
    refine ⟨y, ⟨hy, s, c, hs, hc, ?_⟩, hyx⟩
    rw [← hk, LinearMap.mem_ker, map_sub, map_sum]
    simpa only [map_smul, restrictedRootVector, hyx] using sub_eq_zero.mpr hcx.symm

/-- The same restriction statement for the nonnegative projected-root cone. -/
theorem splitComponent_image_rootNonnegCone
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hbij : Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J) Set.univ)
    (hfin : (simpleRelativeRoots i ν).Finite) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
        projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J) =
      restrictedRootNonnegCone i ν J f hfin := by
  classical
  have hk := ker_restrictReal_eq_rootSpan_of_range hA hT f J hrange
  have hS : (simpleRelativeRoots i ν \ J).Finite := hfin.subset Set.sdiff_subset
  let s := hS.toFinset
  have hs : (s : Set (characterLattice T)) = simpleRelativeRoots i ν \ J :=
    hS.coe_toFinset
  let v : characterLattice T → Vstar T := fun α => (1 : ℝ) ⊗ₜ[ℤ] α
  have hv : v '' (s : Set (characterLattice T)) =
      v '' (simpleRelativeRoots i ν \ J) := by rw [hs]
  have hf := hS.image v
  have hcone : (PointedCone.hull ℝ (v '' (simpleRelativeRoots i ν \ J)) : Set (Vstar T)) =
      RootCombination.nonneg (v '' (simpleRelativeRoots i ν \ J)) hf := by
    rw [← RootCombination.nonnegCone_eq_hull hf]
    rfl
  ext x
  constructor
  · rintro ⟨y, ⟨hy, z, hz, hdiff⟩, rfl⟩
    change z ∈ (PointedCone.hull ℝ (v '' (simpleRelativeRoots i ν \ J)) :
      Set (Vstar T)) at hz
    rw [hcone] at hz
    obtain ⟨c, hc, hcz⟩ := (RootCombination.mem_nonneg_iff_family hf s v hv).mp hz
    apply (mem_restrictedRootNonnegCone_iff_roots i ν J f hfin s hs).mpr
    refine ⟨c, hc, ?_⟩
    rw [← hk, LinearMap.mem_ker, map_sub, ← hcz, map_sum] at hdiff
    simpa only [map_smul, v, restrictedRootVector] using (sub_eq_zero.mp hdiff).symm
  · intro hx
    obtain ⟨c, hc, hcx⟩ :=
      (mem_restrictedRootNonnegCone_iff_roots i ν J f hfin s hs).mp hx
    obtain ⟨y, hy, hyx⟩ := hbij.surjOn (Set.mem_univ x)
    refine ⟨y, ⟨hy, ∑ α ∈ s, c α • v α, ?_, ?_⟩, hyx⟩
    · change (∑ α ∈ s, c α • v α) ∈
        (PointedCone.hull ℝ (v '' (simpleRelativeRoots i ν \ J)) : Set (Vstar T))
      rw [hcone]
      exact (RootCombination.mem_nonneg_iff_family hf s v hv).mpr ⟨c, hc, rfl⟩
    · rw [← hk, LinearMap.mem_ker, map_sub, map_sum]
      simpa only [map_smul, v, restrictedRootVector, hyx] using sub_eq_zero.mpr hcx.symm

end Restriction

end Langlands.GroupScheme
