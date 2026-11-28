import Langlands.AlgebraicGeometry.HenselianBirationalSolution.Glue
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # The glued scheme is separated

The closure of the graph of each transition map is closed in `Y ×_S Y`, so the glued scheme
satisfies the uniqueness part of the valuative criterion: two morphisms from the spectrum of a
valuation ring which agree on the generic point lie, near the closed point, in charts `i` and `j`,
and the closedness of the graph forces them to correspond under the transition map.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

/-- The spectrum of the fraction field of a domain is dominant over the spectrum of the domain. -/
theorem isDominant_specMap_fractionRing (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  have : DenseRange (PrimeSpectrum.comap (algebraMap R K)) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
      exact bot_le)
  exact ⟨this⟩

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g] [QuasiCompact g]
  (H : GlueHyp m) {ι : Type u} (τ : ι → Translation m)

namespace Glue

/-- A morphism from a local scheme lands in a chart containing the image of the closed point. -/
theorem range_subset_chart {R : Type u} [CommRing R] [IsLocalRing R]
    (a : Spec (CommRingCat.of R) ⟶ glued H τ) (i : ι)
    (hi : a (IsLocalRing.closedPoint R) ∈ Set.range (chart H τ i)) :
    Set.range a ⊆ Set.range (chart H τ i) := by
  rintro _ ⟨p, rfl⟩
  exact (chart H τ i).isOpenEmbedding.isOpen_range.stableUnderGeneralization
    ((IsLocalRing.specializes_closedPoint (R := R) p).map a.continuous) hi

/-- Two morphisms from the spectrum of a local domain into the glued scheme which agree on the
generic point and over `S` are equal. -/
theorem eq_of_comp_specMap_eq {R K : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (a b : Spec (CommRingCat.of R) ⟶ glued H τ)
    (hab : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b)
    (hg : a ≫ toBase H τ = b ≫ toBase H τ) : a = b := by
  set η := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsDominant η := isDominant_specMap_fractionRing R K
  set c : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  obtain ⟨i, y, hy⟩ := exists_chart H τ (a c)
  obtain ⟨j, z, hz⟩ := exists_chart H τ (b c)
  set a₁ := IsOpenImmersion.lift (chart H τ i) a (range_subset_chart H τ a i ⟨y, hy⟩)
  set b₁ := IsOpenImmersion.lift (chart H τ j) b (range_subset_chart H τ b j ⟨z, hz⟩)
  have ha₁ : a₁ ≫ chart H τ i = a := IsOpenImmersion.lift_fac _ _ _
  have hb₁ : b₁ ≫ chart H τ j = b := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨w, hw1, hw2⟩ := exists_of_chart_eq H τ i j (η ≫ a₁) (η ≫ b₁)
    (by rw [Category.assoc, Category.assoc, ha₁, hb₁, hab])
  have hg' : a₁ ≫ g = b₁ ≫ g := by
    calc a₁ ≫ g = a₁ ≫ chart H τ i ≫ toBase H τ := by rw [chart_toBase]
      _ = a ≫ toBase H τ := by rw [← Category.assoc, ha₁]
      _ = b ≫ toBase H τ := hg
      _ = b₁ ≫ g := by rw [← hb₁, Category.assoc, chart_toBase]
  set P := pullback.lift a₁ b₁ hg'
  have hP : η ≫ P = w ≫ (Translation.chartIso (τ i) (τ j) H).inv ≫ (Translation.graph (τ i) (τ j)).imageι := by
    rw [← Translation.graph_chartTrans]
    apply pullback.hom_ext
    · simp [P, hw1]
    · simp [P, hw2]
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have hPt : P (η t) ∈ Set.range (Translation.graph (τ i) (τ j)).imageι := by
    rw [← Scheme.Hom.comp_apply, hP]
    exact ⟨_, rfl⟩
  have hPc : P c ∈ Set.range (Translation.graph (τ i) (τ j)).imageι :=
    ((IsLocalRing.specializes_closedPoint (R := R) (η t)).map P.continuous).mem_closed
      (Translation.isClosed_range_imageι (τ i) (τ j)) hPt
  have hac : a₁ c ∈ V H τ i j := by
    obtain ⟨γ, hγ⟩ := hPc
    refine ⟨γ, ?_⟩
    rw [Translation.pr₁, Scheme.Hom.comp_apply, hγ, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  have hra : Set.range a₁ ⊆ Set.range (V H τ i j).ι := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (V H τ i j).isOpen.stableUnderGeneralization
      ((IsLocalRing.specializes_closedPoint (R := R) p).map a₁.continuous) hac
  set a₂ := IsOpenImmersion.lift (V H τ i j).ι a₁ hra
  have ha₂ : a₂ ≫ (V H τ i j).ι = a₁ := IsOpenImmersion.lift_fac _ _ _
  have hηa₂ : η ≫ a₂ = w := by
    rw [← cancel_mono (V H τ i j).ι, Category.assoc, ha₂, hw1]
  have ha₂ψ : a₂ ≫ ψ H τ i j = b₁ := by
    refine ext_of_isDominant_of_isSeparated g ?_ η ?_
    · rw [Category.assoc, Translation.chartTrans_comp_g, reassoc_of% ha₂, hg']
    · rw [reassoc_of% hηa₂, hw2]
  rw [← ha₁, ← hb₁, ← ha₂, Category.assoc, ← ψ_chart, reassoc_of% ha₂ψ]

/-- The glued scheme is separated over `S`. -/
theorem isSeparated_toBase : IsSeparated (toBase H τ) := by
  apply IsSeparated.of_valuativeCriterion
  intro VS
  constructor
  intro l₁ l₂
  have h := eq_of_comp_specMap_eq H τ (K := VS.K) l₁.l l₂.l
    (by rw [l₁.fac_left, l₂.fac_left]) (by rw [l₁.fac_right, l₂.fac_right])
  cases l₁
  cases l₂
  congr

end Glue

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
