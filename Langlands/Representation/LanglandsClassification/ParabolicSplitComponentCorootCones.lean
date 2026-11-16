import Langlands.Representation.LanglandsClassification.ParabolicChamberStatements

/-! # Finite coroot combinations on the split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

variable {k : Type u} [Field k]
  {T A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {D : RelativeRootReflectionData i}
  {J : Set (characterLattice T)} {f : A ⟶ T}

/-- The singleton projected-coroot condition has one prescribed original coroot. -/
theorem mem_projectedCoroots_singleton_iff (α : relativeRoots i) (v : V T) :
    v ∈ D.projectedCoroots J {α.1} ↔
      v ∈ rootAnnihilator T J ∧
        D.realCoroot α - v ∈ Submodule.span ℝ (D.realCorootsOf J) := by
  constructor
  · rintro ⟨hv, z, ⟨α', hα', rfl⟩, hz⟩
    have he : α' = α := Subtype.ext (Set.mem_singleton_iff.mp hα')
    subst α'
    exact ⟨hv, hz⟩
  · rintro ⟨hv, hdiff⟩
    exact ⟨hv, D.realCoroot α, ⟨α, Set.mem_singleton _, rfl⟩, hdiff⟩

/-- Distinct restricted roots identify the root labeling a restricted coroot. -/
theorem restrictedParabolicCoroot_at_iff
    (hsep : ∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J,
      restrictedRootVector f α = restrictedRootVector f α' → α = α')
    {α : characterLattice T} (hα : α ∈ simpleRelativeRoots i ν \ J) (w : V A) :
    IsRestrictedParabolicCoroot i ν D J f (restrictedRootVector f α) w ↔
      cocharacterMapReal f w ∈ D.projectedCoroots J {α} := by
  constructor
  · rintro ⟨α', hα', he, hw⟩
    have he' := hsep α' hα' α hα he
    subst α'
    exact hw
  · intro hw
    exact ⟨α, hα, rfl, hw⟩

/-- Reindexing by the underlying roots preserves the projected-coroot sum modulo `J`. -/
theorem splitComponent_coroot_sum_difference
    [DecidableEq (characterLattice T)]
    (t : Finset (relativeRoots i)) (c : characterLattice T → ℝ)
    (w : characterLattice T → V A)
    (hw : ∀ α ∈ t, cocharacterMapReal f (w α.1) ∈ D.projectedCoroots J {α.1}) :
    ∑ α ∈ t, c α.1 • D.realCoroot α -
        cocharacterMapReal f (∑ α ∈ t.image Subtype.val, c α • w α) ∈
      Submodule.span ℝ (D.realCorootsOf J) := by
  classical
  rw [map_sum, Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)]
  simp_rw [map_smul]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  exact Submodule.sum_mem _ fun α hα =>
    Submodule.smul_mem _ _ ((mem_projectedCoroots_singleton_iff α _).mp (hw α hα)).2

/-- Transport a finite coroot combination through the cocharacter embedding.
The coefficient predicate may be strict positivity or nonnegativity. -/
theorem splitComponent_corootCombination_iff
    (hinj : Function.Injective (cocharacterMapReal f))
    (hrange : (cocharacterMapReal f).range = rootAnnihilator T J)
    (hcompl : IsCompl (rootAnnihilator T J) (Submodule.span ℝ (D.realCorootsOf J)))
    (hlift : ∀ α ∈ simpleRelativeRoots i ν \ J,
      ∃ w : V A, cocharacterMapReal f w ∈ D.projectedCoroots J {α})
    (hsep : ∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J,
      restrictedRootVector f α = restrictedRootVector f α' → α = α')
    (P : ℝ → Prop) (v : V A) :
    (cocharacterMapReal f v ∈ rootAnnihilator T J ∧
      ∃ (t : Finset (relativeRoots i)) (c : relativeRoots i → ℝ),
        (∀ α : relativeRoots i, α ∈ t ↔ α.1 ∈ simpleRelativeRoots i ν \ J) ∧
        (∀ α ∈ t, P (c α)) ∧
        ∑ α ∈ t, c α • D.realCoroot α - cocharacterMapReal f v ∈
          Submodule.span ℝ (D.realCorootsOf J)) ↔
    ∃ (s : Finset (characterLattice T)) (c : characterLattice T → ℝ)
        (w : characterLattice T → V A),
      (s : Set (characterLattice T)) = simpleRelativeRoots i ν \ J ∧
      (∀ α ∈ s, P (c α) ∧
        IsRestrictedParabolicCoroot i ν D J f (restrictedRootVector f α) (w α)) ∧
      v = ∑ α ∈ s, c α • w α := by
  classical
  constructor
  · rintro ⟨hv, t, c, ht, hc, hdiff⟩
    let s := t.image Subtype.val
    have hs : (s : Set (characterLattice T)) = simpleRelativeRoots i ν \ J := by
      ext α
      constructor
      · intro hα
        obtain ⟨α', hα', rfl⟩ := Finset.mem_image.mp hα
        exact (ht α').mp hα'
      · intro hα
        exact Finset.mem_image.mpr
          ⟨⟨α, simpleRelativeRoots_subset_relativeRoots i ν hα.1⟩, (ht _).mpr hα, rfl⟩
    let d := Function.extend Subtype.val c (fun _ : characterLattice T => (0 : ℝ))
    have hd (α : relativeRoots i) : d α.1 = c α :=
      Subtype.val_injective.extend_apply c _ α
    have hwex : ∀ α : characterLattice T,
        ∃ w : V A, α ∈ simpleRelativeRoots i ν \ J →
          cocharacterMapReal f w ∈ D.projectedCoroots J {α} := by
      intro α
      by_cases hα : α ∈ simpleRelativeRoots i ν \ J
      · obtain ⟨w, hw⟩ := hlift α hα
        exact ⟨w, fun _ => hw⟩
      · exact ⟨0, fun h => (hα h).elim⟩
    choose w hw using hwex
    have hsum := splitComponent_coroot_sum_difference t d w
      (fun α hα => hw α.1 ((ht α).mp hα))
    simp_rw [hd] at hsum
    have hN : cocharacterMapReal f v - cocharacterMapReal f (∑ α ∈ s, d α • w α) ∈
        Submodule.span ℝ (D.realCorootsOf J) := by
      convert (Submodule.span ℝ (D.realCorootsOf J)).sub_mem hsum hdiff using 1; abel
    have hK : cocharacterMapReal f v - cocharacterMapReal f (∑ α ∈ s, d α • w α) ∈
        rootAnnihilator T J := (rootAnnihilator T J).sub_mem hv
          (hrange ▸ LinearMap.mem_range_self _ _)
    have he := hinj (sub_eq_zero.mp ((Submodule.disjoint_def.mp hcompl.disjoint) _ hK hN))
    refine ⟨s, d, w, hs, ?_, he⟩
    intro α hα
    obtain ⟨α', hα', rfl⟩ := Finset.mem_image.mp hα
    exact ⟨by rw [hd]; exact hc α' hα',
      α', (ht α').mp hα', rfl, hw α'.1 ((ht α').mp hα')⟩
  · rintro ⟨s, c, w, hs, hw, rfl⟩
    let t := s.subtype (fun α => α ∈ relativeRoots i)
    have ht (α : relativeRoots i) :
        α ∈ t ↔ α.1 ∈ simpleRelativeRoots i ν \ J := by
      simp only [t, Finset.mem_subtype, ← hs, Finset.mem_coe]
    have himage : t.image Subtype.val = s := by
      ext α
      constructor
      · intro hα
        obtain ⟨α', hα', rfl⟩ := Finset.mem_image.mp hα
        exact Finset.mem_subtype.mp hα'
      · intro hα
        have hαS : α ∈ simpleRelativeRoots i ν \ J := hs ▸ hα
        exact Finset.mem_image.mpr
          ⟨⟨α, simpleRelativeRoots_subset_relativeRoots i ν hαS.1⟩,
            Finset.mem_subtype.mpr hα, rfl⟩
    refine ⟨hrange ▸ LinearMap.mem_range_self _ _, t, fun α => c α.1, ht,
      fun α hα => (hw α.1 (Finset.mem_subtype.mp hα)).1, ?_⟩
    have hsum := splitComponent_coroot_sum_difference t c w (fun α hα =>
      (restrictedParabolicCoroot_at_iff hsep ((ht α).mp hα) _).mp
        (hw α.1 (Finset.mem_subtype.mp hα)).2)
    rwa [himage] at hsum

/-- The coroot hull can be written as a family with one nonnegative coefficient for
each selected root, even when two real coroot vectors coincide. -/
theorem projectedCorootNonnegCone_iff_family
    {S : Set (characterLattice T)} (hS : S.Finite) (v : V T) :
    v ∈ projectedCorootNonnegCone i D J S ↔
      v ∈ rootAnnihilator T J ∧
      ∃ (t : Finset (relativeRoots i)) (c : relativeRoots i → ℝ),
        (∀ α : relativeRoots i, α ∈ t ↔ α.1 ∈ S) ∧
        (∀ α ∈ t, 0 ≤ c α) ∧
        ∑ α ∈ t, c α • D.realCoroot α - v ∈
          Submodule.span ℝ (D.realCorootsOf J) := by
  classical
  constructor
  · rintro ⟨hv, z, hz, hdiff⟩
    let t := hS.toFinset.subtype (fun α => α ∈ relativeRoots i)
    have ht (α : relativeRoots i) : α ∈ t ↔ α.1 ∈ S := by simp [t]
    have hset : D.realCoroot '' (t : Set (relativeRoots i)) = D.realCorootsOf S := by
      ext x
      simp only [Set.mem_image, Finset.mem_coe, ht, RelativeRootReflectionData.realCorootsOf,
        Set.mem_ofPred_eq]
    have hf : (D.realCorootsOf S).Finite := hset ▸ t.finite_toSet.image D.realCoroot
    have hcone : (PointedCone.hull ℝ (D.realCorootsOf S) : Set (V T)) =
        RootCombination.nonneg (D.realCorootsOf S) hf := by
      rw [← RootCombination.nonnegCone_eq_hull hf]
      rfl
    change z ∈ (PointedCone.hull ℝ (D.realCorootsOf S) : Set (V T)) at hz
    rw [hcone] at hz
    obtain ⟨c, hc, hcz⟩ := (RootCombination.mem_nonneg_iff_family hf t D.realCoroot hset).mp hz
    exact ⟨hv, t, c, ht, hc, hcz ▸ hdiff⟩
  · rintro ⟨hv, t, c, ht, hc, hdiff⟩
    refine ⟨hv, ∑ α ∈ t, c α • D.realCoroot α, ?_, hdiff⟩
    exact Submodule.sum_mem _ fun α hα =>
      PointedCone.smul_mem _ (hc α hα)
        (PointedCone.subset_hull ⟨α, (ht α).mp hα, rfl⟩)

end Langlands.GroupScheme
