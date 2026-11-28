import Langlands.AlgebraicGeometry.DvrSmoothening.DefectBoundStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.Induction
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal

/-! # Smoothenings from the affine lemmas on the defect of smoothness -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- If `g` is an isomorphism over an open `W` of its target, then its base change along a morphism
with image in `W` is an isomorphism. -/
theorem isIso_pullback_snd_of_range_subset {X₁ X T : Scheme.{u}} (g : X₁ ⟶ X) (W : X.Opens)
    [IsIso (g ∣_ W)] (h : T ⟶ X) (hh : Set.range h ⊆ W) : IsIso (pullback.snd g h) := by
  obtain ⟨h', rfl⟩ : ∃ h' : T ⟶ W, h = h' ≫ W.ι :=
    ⟨IsOpenImmersion.lift W.ι h (by rwa [Scheme.Opens.range_ι]),
      (IsOpenImmersion.lift_fac _ _ _).symm⟩
  have : IsIso (pullback.snd g W.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
    infer_instance
  have h2 : IsIso ((pullbackLeftPullbackSndIso g W.ι h').hom ≫ pullback.snd g (h' ≫ W.ι)) := by
    rw [pullbackLeftPullbackSndIso_hom_snd]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullbackLeftPullbackSndIso g W.ι h').hom _

/-- If `g` is an isomorphism over an open `W` containing the image of the base change of `f`
along `j`, then the base change of `g` along `j` is an isomorphism. -/
theorem isIso_pullback_map_of_range_subset {X₁ X S T : Scheme.{u}} (g : X₁ ⟶ X) (f : X ⟶ S)
    (j : T ⟶ S) (W : X.Opens) [IsIso (g ∣_ W)] (hW : Set.range (pullback.fst f j) ⊆ W) :
    IsIso (pullback.map (g ≫ f) j f j g (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])) := by
  have := isIso_pullback_snd_of_range_subset g W (pullback.fst f j) hW
  have e : (pullbackRightPullbackFstIso f j g).hom ≫
      pullback.map (g ≫ f) j f j g (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp]) = pullback.snd g (pullback.fst f j) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullbackRightPullbackFstIso_hom_fst_assoc]
      exact pullback.condition
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id,
        pullbackRightPullbackFstIso_hom_snd]
  have h2 : IsIso ((pullbackRightPullbackFstIso f j g).hom ≫
      pullback.map (g ≫ f) j f j g (𝟙 _) (𝟙 _) (by rw [Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])) := by
    rw [e]
    infer_instance
  exact IsIso.of_isIso_comp_left (pullbackRightPullbackFstIso f j g).hom _

/-- The restriction of a morphism to its smooth locus is smooth. -/
theorem smooth_smoothLocus_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Smooth (f.smoothLocus.ι ≫ f) := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Opens.ι_preimage_self]

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The fraction field of a discrete valuation ring is its localization away from a
uniformizer. -/
theorem isLocalization_away_of_irreducible (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  have hinj := IsFractionRing.injective R K
  have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  apply IsLocalization.Away.mk
  · exact IsUnit.mk0 _ hϖK
  · intro s
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨m, a * ↑v⁻¹, ?_⟩
    have hv' : algebraMap R K (v : R) * algebraMap R K (↑v⁻¹ : R) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hvK : algebraMap R K (v : R) ≠ 0 := fun h0 => by simp [h0] at hv'
    rw [hv, map_mul, map_mul, map_pow]
    field_simp
    rw [mul_assoc, hv', mul_one]
  · intro a b h
    exact ⟨0, by simpa using hinj h⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The point of the spectrum of the fraction field maps to the generic point. -/
theorem specMap_algebraMap_fraction_apply (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (z : Spec (CommRingCat.of K)) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R K))) z).asIdeal = ⊥ := by
  have hz : (show PrimeSpectrum K from z).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right z.2.ne_top
  change Ideal.comap _ (show PrimeSpectrum K from z).asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

/-- A smooth generic fibre gives smoothness at all points over the generic point. -/
theorem genericallySmooth_of_smooth_pullback (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f]
    (hs : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    GenericallySmooth f := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := isLocalization_away_of_irreducible K hϖ
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    IsOpenImmersion.of_isLocalization ϖ
  intro x hx
  have hxr : f x ∈ (Spec.map (CommRingCat.ofHom (algebraMap R K))).opensRange := by
    exact ⟨(show Spec (CommRingCat.of K) from IsLocalRing.closedPoint K),
      PrimeSpectrum.ext ((specMap_algebraMap_fraction_apply K _).trans hx.symm)⟩
  obtain ⟨y, rfl⟩ : x ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R K)))) := by
    rw [IsOpenImmersion.range_pullbackFst]
    exact hxr
  have : Smooth (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ f) := by
    rw [pullback.condition]
    infer_instance
  have h1 := Scheme.Hom.preimage_smoothLocus_eq
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) f
  rw [Scheme.Hom.smoothLocus_eq_top
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ f)] at h1
  have : y ∈ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ⁻¹ᵁ
      f.smoothLocus := by
    rw [h1]
    trivial
  exact this

/-- The defect of smoothness is bounded on all points of a quasi-compact scheme of finite type
over `R` with smooth generic fibre. -/
theorem exists_defect_bound (hDB : DefectBoundStatement.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [QuasiCompact f] {ϖ : R}
    (hϖ : Irreducible ϖ) (hf : GenericallySmooth f) :
    ∃ n : ℕ, ∀ P : TestPoint X f, P.defect < n := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hC : ∀ C : AffineChart X, ∃ n : ℕ, ∀ P : TestPoint X f,
      ∀ h : P.special ∈ C.ι.opensRange, P.defect ≤ n := by
    intro C
    let := (C.base f).toAlgebra
    have := C.finiteType_base f
    obtain ⟨n, hn⟩ := hDB R C.ring ϖ hϖ (C.smooth_away f hϖ hf)
    exact ⟨n, fun P h => (P.defect_eq_pointDefect f C h).trans_le
      (hn P.ring P.ram (C.pointAlgHom f P h))⟩
  choose N hN using hC
  choose Cx hCx using fun x : X => AffineChart.exists_mem x
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((Cx x).ι.opensRange : Set X)) (fun x => (Cx x).ι.opensRange.2)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hCx x⟩)
  refine ⟨t.sup (fun x => N (Cx x)) + 1, fun P => ?_⟩
  obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ P.special))
  calc P.defect ≤ N (Cx x) := hN _ P hx
    _ ≤ (t.sup (fun x => N (Cx x)) : ℕ) := by exact_mod_cast Finset.le_sup (f := fun x => N (Cx x)) hxt
    _ < ((t.sup (fun x => N (Cx x)) + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self _

/-- Existence of smoothenings over discrete valuation rings, from the affine lemmas on the
defect of smoothness and the existence of blow-ups with charts. -/
theorem dvrSmoothening_of (hDZ : DefectZeroSmoothAtStatement.{u})
    (hDD : DilatationDefectStatement.{u}) (hGC : GoodChartStatement.{u})
    (hDB : DefectBoundStatement.{u}) (hBC : BlowupChartStatement.{u}) :
    DvrSmootheningStatement.{u} := by
  intro R K _ _ _ _ _ _ X f hft hqc hsm
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hgen : GenericallySmooth f := genericallySmooth_of_smooth_pullback K f hsm
  obtain ⟨n, hn⟩ := exists_defect_bound hDB f hϖ hgen
  obtain ⟨X', g, hg, hiso, hres⟩ :=
    claim hDZ hDD hGC hBC hϖ n X f hgen (fun _ => True) (fun P _ => hn P)
  refine ⟨X', g, hg, ?_, ?_⟩
  · apply isIso_pullback_map_of_range_subset g f (Spec.map (CommRingCat.ofHom (algebraMap R K)))
      (centre f fun _ => True).compl
    rintro _ ⟨z, rfl⟩
    apply not_mem_centre_of_generic
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact specMap_algebraMap_fraction_apply K _
  · intro R' _ _ _ _ _ hram a ha
    obtain ⟨a₁, ha₁, hs⟩ := hres ⟨R', hram, a, ha⟩ trivial
    refine ⟨(g ≫ f).smoothLocus, IsOpenImmersion.lift (g ≫ f).smoothLocus.ι a₁ ?_, ?_, ?_⟩
    · rw [Scheme.Opens.range_ι]
      exact range_subset_of_closedPoint_mem a₁ _ hs
    · exact smooth_smoothLocus_ι (g ≫ f)
    · rw [IsOpenImmersion.lift_fac_assoc]
      exact ha₁

end Langlands.AlgebraicGeometry.DvrSmoothening
