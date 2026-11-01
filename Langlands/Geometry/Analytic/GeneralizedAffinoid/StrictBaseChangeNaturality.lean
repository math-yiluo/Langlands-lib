import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChangeRetraction
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Embedding
import Langlands.Geometry.Analytic.BoundedQuotient

/-! # Variable inclusions commute with strict base change and descent -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

namespace GeneralizedTateAlgebra

variable {σ : Type w} {τ : Type z}
  {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]

/-- The coefficient-preserving inclusion of a set of strict Tate variables. -/
def strictRename (e : σ ↪ τ) :
    BoundedAlgHom L (StrictTateAlgebra σ L) (StrictTateAlgebra τ L) where
  toAlgHom := (unitAlgEquiv L).toAlgHom.comp
    ((rename (PositivePolyradius.unit σ) (PositivePolyradius.unit τ) e
      (fun _ => rfl) L).comp (unitAlgEquiv L).symm.toAlgHom)
  bounded := ⟨1, zero_lt_one, fun f => by
    change ‖unitAlgEquiv L (rename (PositivePolyradius.unit σ)
      (PositivePolyradius.unit τ) e (fun _ => rfl) L ((unitAlgEquiv L).symm f))‖ ≤
        1 * ‖f‖
    rw [norm_unitAlgEquiv, one_mul]
    exact ((norm_rename (PositivePolyradius.unit σ) (PositivePolyradius.unit τ)
      e (fun _ => rfl) L ((unitAlgEquiv L).symm f)).trans
        (norm_unitAlgEquiv L ((unitAlgEquiv L).symm f)).symm).le⟩

@[simp] theorem series_strictRename (e : σ ↪ τ) (f : StrictTateAlgebra σ L) :
    StrictTateAlgebra.series τ L (strictRename e f) =
      MvPowerSeries.rename e (StrictTateAlgebra.series σ L f) := rfl

omit [IsUltrametricDist L] in
theorem scale_embDomain (e : σ ↪ τ) (c : σ → L) (b : τ → L)
    (he : ∀ i, b (e i) = c i) (d : σ →₀ ℕ) :
    scale b (Finsupp.embDomain e d) = scale c d := by
  simp only [scale, Finsupp.prod_embDomain, he]

variable (r : PositivePolyradius σ) (s : PositivePolyradius τ)
  (e : σ ↪ τ) (he : ∀ i, s (e i) = r i)
  (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : σ → L} (hc : ∀ i, ‖c i‖ = r i)
  {b : τ → L} (hb : ∀ i, ‖b i‖ = s i)
  (hbc : ∀ i, b (e i) = c i)

include hbc in
/-- Scalar extension and variable normalization commute with variable inclusion. -/
theorem baseChange_rename (f : GeneralizedTateAlgebra r K) :
    baseChange s ι hb hι (rename r s e he K f) =
      strictRename e (baseChange r ι hc hι f) := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (StrictTateAlgebra.series τ L
      (baseChange s ι hb hι (rename r s e he K f))) =
    MvPowerSeries.coeff d (StrictTateAlgebra.series τ L
      (strictRename e (baseChange r ι hc hι f)))
  by_cases hd : d ∈ Set.range (Finsupp.embDomain e)
  · obtain ⟨a, rfl⟩ := hd
    rw [coeff_baseChange, coeff_embDomain_rename, series_strictRename,
      MvPowerSeries.coeff_embDomain_rename, coeff_baseChange,
      scale_embDomain e c b hbc]
  · have hz : MvPowerSeries.coeff d (MvPowerSeries.rename e f.val) = 0 :=
      MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact hd)
    rw [coeff_baseChange, series_strictRename,
      MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact hd)]
    change scale b d * ι (MvPowerSeries.coeff d (MvPowerSeries.rename e f.val)) = 0
    rw [hz, map_zero, mul_zero]

variable (π : L →+ K) {D : ℝ} (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

include hbc in
/-- Coefficient descent commutes with coefficient-preserving variable inclusion. -/
theorem descend_strictRename (f : StrictTateAlgebra σ L) :
    descend s hb π hπD (strictRename e f) =
      rename r s e he K (descend r hc π hπD f) := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change MvPowerSeries.coeff d (series s K (descend s hb π hπD (strictRename e f))) =
    MvPowerSeries.coeff d (series s K (rename r s e he K (descend r hc π hπD f)))
  by_cases hd : d ∈ Set.range (Finsupp.embDomain e)
  · obtain ⟨a, rfl⟩ := hd
    rw [coeff_descend, series_strictRename, MvPowerSeries.coeff_embDomain_rename,
      coeff_embDomain_rename, coeff_descend, scale_embDomain e c b hbc]
  · rw [coeff_descend, series_strictRename,
      MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact hd), mul_zero, map_zero, series_rename,
      MvPowerSeries.coeff_rename_eq_zero e _ (by
        rw [← funext (Finsupp.embDomain_eq_mapDomain e)]
        exact hd)]

end GeneralizedTateAlgebra

namespace PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (A B : PresentedAffinoidAlgebra K)
  (e : Fin A.arity ↪ Fin B.arity)
  (he : ∀ i, B.polyradius (e i) = A.polyradius i)
  (hI : ∀ f ∈ A.ideal, rename A.polyradius B.polyradius e he K f ∈ B.ideal)

/-- The quotient map induced by an inclusion of variables respecting the ideals. -/
def renameHom : BoundedAlgHom K A B := by
  letI := A.ideal_closed
  exact BoundedAlgHom.liftQuotient K A.ideal
    ((presentationMap K B).comp (boundedRename A.polyradius B.polyradius e he K))
    (fun f hf => (presentationMap_eq_zero_iff K B _).mpr (hI f hf))

@[simp] theorem renameHom_presentationMap (f : GeneralizedTateAlgebra A.polyradius K) :
    renameHom A B e he hI (presentationMap K A f) =
      presentationMap K B (rename A.polyradius B.polyradius e he K f) := rfl

variable (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ i, ‖c i‖ = A.polyradius i)
  {b : Fin B.arity → L} (hb : ∀ i, ‖b i‖ = B.polyradius i)
  (hbc : ∀ i, b (e i) = c i)

/-- The actual bounded map between the two strict base-change quotients. -/
def strictBaseChangeRenameHom :
    BoundedAlgHom L (strictBaseChange A ι hι hc) (strictBaseChange B ι hι hb) := by
  letI := (strictBaseChange A ι hι hc).ideal_closed
  let γ := (PresentedStrictAffinoidAlgebra.presentationMap L
    (strictBaseChange B ι hι hb)).comp (strictRename e)
  have hmap : Ideal.map (baseChange A.polyradius ι hc hι) A.ideal ≤
      RingHom.ker γ.toAlgHom.toRingHom := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change γ (baseChange A.polyradius ι hc hι f) = 0
    change PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange B ι hι hb)
      (strictRename e (baseChange A.polyradius ι hc hι f)) = 0
    rw [← baseChange_rename A.polyradius B.polyradius e he ι hι hc hb hbc]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (subset_closure (Ideal.mem_map_of_mem _ (hI f hf)))
  exact BoundedAlgHom.liftQuotient L (strictBaseChange A ι hι hc).ideal γ
    (γ.annihilates_closure _ fun f hf => hmap hf)

@[simp] theorem strictBaseChangeRenameHom_presentationMap
    (f : StrictTateAlgebra (Fin A.arity) L) :
    strictBaseChangeRenameHom A B e he hI ι hι hc hb hbc
        (PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange A ι hι hc) f) =
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange B ι hι hb)
        (strictRename e f) := rfl

/-- Both actual maps from the original quotient to the larger strict quotient agree. -/
theorem strictBaseChangeRenameHom_strictBaseChangeHom (a : A) :
    strictBaseChangeRenameHom A B e he hI ι hι hc hb hbc
        (strictBaseChangeHom A ι hι hc a) =
      strictBaseChangeHom B ι hι hb (renameHom A B e he hI a) := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K A a
  rw [strictBaseChangeHom_presentationMap, strictBaseChangeRenameHom_presentationMap,
    renameHom_presentationMap, strictBaseChangeHom_presentationMap,
    baseChange_rename A.polyradius B.polyradius e he ι hι hc hb hbc]

variable (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

/-- The additive quotient retractions commute with the actual variable inclusion. -/
theorem strictBaseChangeRetraction_renameHom (a : strictBaseChange A ι hι hc) :
    strictBaseChangeRetraction B ι hι hb π hπ hD hπD
        (strictBaseChangeRenameHom A B e he hI ι hι hc hb hbc a) =
      renameHom A B e he hI (strictBaseChangeRetraction A ι hι hc π hπ hD hπD a) := by
  obtain ⟨f, rfl⟩ : ∃ f : StrictTateAlgebra (Fin A.arity) L,
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange A ι hι hc) f = a :=
    PresentedStrictAffinoidAlgebra.presentationMap_surjective L
      (strictBaseChange A ι hι hc) a
  rw [strictBaseChangeRenameHom_presentationMap,
    strictBaseChangeRetraction_presentationMap, strictBaseChangeRetraction_presentationMap,
    renameHom_presentationMap, descend_strictRename A.polyradius B.polyradius e he
      hc hb hbc π hπD]

end PresentedAffinoidAlgebra

end Langlands.Analytic
