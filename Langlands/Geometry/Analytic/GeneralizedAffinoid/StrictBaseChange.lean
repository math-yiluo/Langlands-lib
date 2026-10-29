import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Topology.Algebra.Ring.Ideal

/-! # Strict base change of weighted quotient presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic

open Filter
open scoped Topology

namespace GeneralizedTateAlgebra

section BaseChange

variable {σ : Type*} (r : PositivePolyradius σ)
  {K : Type u} [NormedField K] {L : Type v} [NormedField L]

/-- The scalar `c ^ d = ∏ i, c i ^ d i` attached to an exponent `d`. -/
def scale (c : σ → L) (d : σ →₀ ℕ) : L :=
  d.prod fun i n => c i ^ n

theorem scale_add (c : σ → L) (d e : σ →₀ ℕ) :
    scale c (d + e) = scale c d * scale c e :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

variable {r} in
theorem norm_scale {c : σ → L} (hc : ∀ i, ‖c i‖ = r i) (d : σ →₀ ℕ) :
    ‖scale c d‖ = r.weight d := by
  simp only [scale, Finsupp.prod, norm_prod, norm_pow, hc, PositivePolyradius.weight]

variable {r} in
theorem scale_ne_zero {c : σ → L} (hc : ∀ i, ‖c i‖ = r i) (d : σ →₀ ℕ) :
    scale c d ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_scale hc]
  exact (r.weight_pos d).ne'

variable [IsUltrametricDist K] [IsUltrametricDist L]
  (ι : K →+* L) {c : σ → L} (hc : ∀ i, ‖c i‖ = r i) (hι : ∀ a, ‖ι a‖ = ‖a‖)

omit [IsUltrametricDist L] in
include hc hι in
/-- Mapping coefficients isometrically and rescaling the variables by `c` turns a
weighted restricted series into a radius-one restricted series. -/
theorem isRestricted_baseChange (f : GeneralizedTateAlgebra r K) :
    MvPowerSeries.IsRestricted (fun _ : σ => (1 : ℝ))
      (MvPowerSeries.rescale c (MvPowerSeries.map ι (series r K f))) := by
  have hf := f.property
  change Tendsto (fun t => ‖MvPowerSeries.coeff t f.val‖ * r.weight t) cofinite (𝓝 0) at hf
  refine hf.congr fun t => ?_
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_map]
  change _ = ‖scale c t * ι (MvPowerSeries.coeff t f.val)‖ * t.prod fun _ n => (1 : ℝ) ^ n
  simp only [norm_mul, norm_scale hc, hι, one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
  exact mul_comm _ _

/-- The coefficientwise base change `f ↦ ∑ c ^ d ι(f_d) X ^ d` into the radius-one
Tate algebra over `L`. -/
def baseChange : GeneralizedTateAlgebra r K →+* StrictTateAlgebra σ L :=
  ((MvPowerSeries.rescale c).comp ((MvPowerSeries.map ι).comp
    (weightedRestrictedSubalgebra r K).val.toRingHom)).codRestrict
      (restrictedSubalgebra σ L) (isRestricted_baseChange r ι hc hι)

theorem coeff_baseChange (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (StrictTateAlgebra.series σ L (baseChange r ι hc hι f)) =
      scale c d * ι (MvPowerSeries.coeff d (series r K f)) := by
  change MvPowerSeries.coeff d (MvPowerSeries.rescale c (MvPowerSeries.map ι f.val)) = _
  rw [MvPowerSeries.coeff_rescale, MvPowerSeries.coeff_map]
  rfl

/-- The base change is an isometry onto its image. -/
theorem norm_baseChange (f : GeneralizedTateAlgebra r K) :
    ‖baseChange r ι hc hι f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (StrictTateAlgebra.norm_le_iff σ L _ (norm_nonneg f)).mpr
    intro d
    rw [coeff_baseChange, norm_mul, norm_scale hc, hι, mul_comm]
    exact weighted_norm_coeff_le r K f d
  · apply (norm_le_iff r K f (norm_nonneg _)).mpr
    intro d
    have h := StrictTateAlgebra.norm_coeff_le σ L (baseChange r ι hc hι f) d
    rwa [coeff_baseChange, norm_mul, norm_scale hc, hι, mul_comm] at h

variable (π : L →+ K) {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

omit [IsUltrametricDist K] [IsUltrametricDist L] in
include hc hπD in
theorem norm_descend_coeff_le (d : σ →₀ ℕ) (x : L) :
    ‖π ((scale c d)⁻¹ * x)‖ * r.weight d ≤ D * ‖x‖ := by
  have hw := r.weight_pos d
  calc ‖π ((scale c d)⁻¹ * x)‖ * r.weight d
      ≤ D * ‖(scale c d)⁻¹ * x‖ * r.weight d :=
        mul_le_mul_of_nonneg_right (hπD _) hw.le
    _ = D * ‖x‖ := by
        rw [norm_mul, norm_inv, norm_scale hc]
        field_simp

omit [IsUltrametricDist K] in
include hc hπD in
theorem isRestricted_descend (g : StrictTateAlgebra σ L) :
    MvPowerSeries.IsRestricted r
      (fun d => π ((scale c d)⁻¹ *
        MvPowerSeries.coeff d (StrictTateAlgebra.series σ L g)) : MvPowerSeries σ K) := by
  have hg := g.property
  change Tendsto (fun t => ‖MvPowerSeries.coeff t g.val‖ * t.prod fun _ n => (1 : ℝ) ^ n)
    cofinite (𝓝 0) at hg
  have hg' : Tendsto (fun t => D * ‖MvPowerSeries.coeff t g.val‖) cofinite (𝓝 0) := by
    simpa [Finsupp.prod] using hg.const_mul D
  apply squeeze_zero (fun t => mul_nonneg (norm_nonneg _) (r.weight_pos t).le) _ hg'
  intro t
  exact norm_descend_coeff_le r hc π hπD t _

/-- The coefficientwise descent `g ↦ ∑ π(c ^ (-d) g_d) X ^ d`, a bounded additive
left inverse of `baseChange`. -/
def descend : StrictTateAlgebra σ L →+ GeneralizedTateAlgebra r K where
  toFun g := ⟨fun d => π ((scale c d)⁻¹ *
    MvPowerSeries.coeff d (StrictTateAlgebra.series σ L g)), isRestricted_descend r hc π hπD g⟩
  map_zero' := by
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro d
    change π ((scale c d)⁻¹ * MvPowerSeries.coeff d (0 : MvPowerSeries σ L)) =
      MvPowerSeries.coeff d (0 : MvPowerSeries σ K)
    simp
  map_add' g h := by
    apply Subtype.ext
    apply MvPowerSeries.ext
    intro d
    change π ((scale c d)⁻¹ * MvPowerSeries.coeff d (g.val + h.val)) =
      π ((scale c d)⁻¹ * MvPowerSeries.coeff d g.val) +
        π ((scale c d)⁻¹ * MvPowerSeries.coeff d h.val)
    rw [map_add, mul_add, map_add]

theorem coeff_descend (g : StrictTateAlgebra σ L) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (series r K (descend r hc π hπD g)) =
      π ((scale c d)⁻¹ * MvPowerSeries.coeff d (StrictTateAlgebra.series σ L g)) :=
  rfl

include hD in
theorem norm_descend_le (g : StrictTateAlgebra σ L) :
    ‖descend r hc π hπD g‖ ≤ D * ‖g‖ := by
  apply (norm_le_iff r K _ (mul_nonneg hD (norm_nonneg g))).mpr
  intro d
  rw [coeff_descend]
  exact (norm_descend_coeff_le r hc π hπD d _).trans
    (mul_le_mul_of_nonneg_left (StrictTateAlgebra.norm_coeff_le σ L g d) hD)

include hD in
theorem continuous_descend : Continuous (descend r hc π hπD) :=
  AddMonoidHomClass.continuous_of_bound (descend r hc π hπD) D (norm_descend_le r hc π hD hπD)

variable (hπ : ∀ a x, π (ι a * x) = a * π x)

include hπ in
/-- Descent is linear over the base-changed coefficients. -/
theorem descend_baseChange_mul (f : GeneralizedTateAlgebra r K) (g : StrictTateAlgebra σ L) :
    descend r hc π hπD (baseChange r ι hc hι f * g) = f * descend r hc π hπD g := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change π ((scale c d)⁻¹ * MvPowerSeries.coeff d
      (StrictTateAlgebra.series σ L (baseChange r ι hc hι f) *
        StrictTateAlgebra.series σ L g)) =
    MvPowerSeries.coeff d (series r K f * series r K (descend r hc π hπD g))
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_antidiagonal] at hp
  rw [coeff_baseChange, coeff_descend, ← hp, scale_add]
  have h1 := scale_ne_zero hc p.1
  have h2 := scale_ne_zero hc p.2
  rw [show (scale c p.1 * scale c p.2)⁻¹ *
      (scale c p.1 * ι (MvPowerSeries.coeff p.1 (series r K f)) *
        MvPowerSeries.coeff p.2 (StrictTateAlgebra.series σ L g)) =
      ι (MvPowerSeries.coeff p.1 (series r K f)) *
        ((scale c p.2)⁻¹ * MvPowerSeries.coeff p.2 (StrictTateAlgebra.series σ L g)) by
    field_simp]
  exact hπ _ _

include hπ in
/-- Descent is a left inverse of base change when `π 1 = 1`. -/
theorem descend_baseChange (hπ1 : π 1 = 1) (f : GeneralizedTateAlgebra r K) :
    descend r hc π hπD (baseChange r ι hc hι f) = f := by
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro d
  change π ((scale c d)⁻¹ * MvPowerSeries.coeff d
      (StrictTateAlgebra.series σ L (baseChange r ι hc hι f))) =
    MvPowerSeries.coeff d (series r K f)
  rw [coeff_baseChange, ← mul_assoc, inv_mul_cancel₀ (scale_ne_zero hc d), one_mul,
    ← mul_one (ι _), hπ, hπ1, mul_one]

include hD hπ in
/-- Descent sends the closure of the ideal generated by base-changed elements of a
closed ideal back into that ideal. -/
theorem descend_mem_of_mem_closure_map (I : Ideal (GeneralizedTateAlgebra r K))
    (hI : IsClosed (I : Set (GeneralizedTateAlgebra r K))) {x : StrictTateAlgebra σ L}
    (hx : x ∈ (Ideal.map (baseChange r ι hc hι) I).closure) :
    descend r hc π hπD x ∈ I := by
  let T : Ideal (StrictTateAlgebra σ L) :=
    { carrier := {x | ∀ g, descend r hc π hπD (g * x) ∈ I}
      add_mem' := fun {x y} hx hy g => by
        rw [mul_add, map_add]
        exact I.add_mem (hx g) (hy g)
      zero_mem' := fun g => by
        rw [mul_zero, map_zero]
        exact I.zero_mem
      smul_mem' := fun a x hx g => by
        rw [smul_eq_mul, ← mul_assoc]
        exact hx (g * a) }
  have hmap : Ideal.map (baseChange r ι hc hι) I ≤ T := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf g
    rw [mul_comm, descend_baseChange_mul r ι hc hι π hπD hπ]
    exact I.mul_mem_right _ hf
  have hsub : (Ideal.map (baseChange r ι hc hι) I : Set (StrictTateAlgebra σ L)) ⊆
      descend r hc π hπD ⁻¹' I := by
    intro y hy
    simpa using hmap hy 1
  exact closure_minimal hsub (hI.preimage (continuous_descend r hc π hD hπD)) hx

end BaseChange

end GeneralizedTateAlgebra

namespace PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (P : PresentedAffinoidAlgebra K) (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin P.arity → L} (hc : ∀ i, ‖c i‖ = P.polyradius i)

/-- The strict presentation over `L` with the same variables, rescaled by `c`, whose
ideal is the closure of the ideal generated by the base-changed relations. -/
def strictBaseChange : PresentedStrictAffinoidAlgebra L where
  arity := P.arity
  ideal := (Ideal.map (baseChange P.polyradius ι hc hι) P.ideal).closure
  ideal_closed := by
    rw [Ideal.coe_closure]
    exact isClosed_closure

/-- The ring homomorphism induced on quotients by `baseChange`. -/
def strictBaseChangeHom : P →+* strictBaseChange P ι hι hc :=
  Ideal.Quotient.lift P.ideal
    ((Ideal.Quotient.mk (strictBaseChange P ι hι hc).ideal).comp
      (baseChange P.polyradius ι hc hι))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (subset_closure (Ideal.mem_map_of_mem _ ha)))

theorem strictBaseChangeHom_presentationMap (f : GeneralizedTateAlgebra P.polyradius K) :
    strictBaseChangeHom P ι hι hc (presentationMap K P f) =
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc)
        (baseChange P.polyradius ι hc hι f) :=
  rfl

/-- The induced map does not increase the quotient norm. -/
theorem norm_strictBaseChangeHom_le (x : P) :
    ‖strictBaseChangeHom P ι hι hc x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, rfl, hf⟩ := exists_representative_norm_lt K P x hε
  rw [strictBaseChangeHom_presentationMap]
  calc _ ≤ ‖baseChange P.polyradius ι hc hι f‖ :=
        Ideal.Quotient.norm_mk_le (strictBaseChange P ι hι hc).ideal _
    _ = ‖f‖ := norm_baseChange P.polyradius ι hc hι f
    _ ≤ _ := hf.le

/-- A bounded coefficient retraction bounds the quotient norm by the base-changed norm. -/
theorem norm_le_mul_norm_strictBaseChangeHom (π : L →+ K)
    (hπ : ∀ a x, π (ι a * x) = a * π x) (hπ1 : π 1 = 1)
    {D : ℝ} (hD : 0 < D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖) (x : P) :
    ‖x‖ ≤ D * ‖strictBaseChangeHom P ι hι hc x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨f, rfl⟩ := presentationMap_surjective K P x
  obtain ⟨g, hg, hgn⟩ : ∃ g : StrictTateAlgebra (Fin P.arity) L,
      Ideal.Quotient.mk (Ideal.map (baseChange P.polyradius ι hc hι) P.ideal).closure g =
        Ideal.Quotient.mk (Ideal.map (baseChange P.polyradius ι hc hι) P.ideal).closure
          (baseChange P.polyradius ι hc hι f) ∧
      ‖g‖ < ‖strictBaseChangeHom P ι hι hc (presentationMap K P f)‖ + ε / D :=
    PresentedStrictAffinoidAlgebra.exists_representative_norm_lt L (strictBaseChange P ι hι hc)
      (strictBaseChangeHom P ι hι hc (presentationMap K P f)) (div_pos hε hD)
  have hdesc := descend_mem_of_mem_closure_map P.polyradius ι hc hι π hD.le hπD hπ P.ideal
    P.ideal_closed (Ideal.Quotient.eq.mp hg)
  rw [map_sub, descend_baseChange P.polyradius ι hc hι π hπD hπ hπ1] at hdesc
  have hx : presentationMap K P (descend P.polyradius hc π hπD g) = presentationMap K P f :=
    Ideal.Quotient.eq.mpr hdesc
  calc ‖presentationMap K P f‖ = ‖presentationMap K P (descend P.polyradius hc π hπD g)‖ := by
        rw [hx]
    _ ≤ ‖descend P.polyradius hc π hπD g‖ := norm_presentationMap_le K P _
    _ ≤ D * ‖g‖ := norm_descend_le P.polyradius hc π hD.le hπD g
    _ ≤ D * (‖strictBaseChangeHom P ι hι hc (presentationMap K P f)‖ + ε / D) :=
        mul_le_mul_of_nonneg_left hgn.le hD.le
    _ = _ := by rw [mul_add, mul_div_cancel₀ _ hD.ne']

/-- Base change along an isometric field embedding with a bounded coefficient retraction
gives a strict presentation over the larger field and a norm-equivalent ring
homomorphism. -/
theorem exists_strictBaseChange
    (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
    (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x) (hπ1 : π 1 = 1)
    {D : ℝ} (hD : 0 < D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)
    (P : PresentedAffinoidAlgebra K) (c : Fin P.arity → L)
    (hc : ∀ i, ‖c i‖ = P.polyradius i) :
    ∃ (Q : PresentedStrictAffinoidAlgebra L) (ψ : P →+* Q) (C : ℝ), 0 < C ∧
      (∀ x, ‖ψ x‖ ≤ ‖x‖) ∧ ∀ x, ‖x‖ ≤ C * ‖ψ x‖ :=
  ⟨strictBaseChange P ι hι hc, strictBaseChangeHom P ι hι hc, D, hD,
    norm_strictBaseChangeHom_le P ι hι hc,
    norm_le_mul_norm_strictBaseChangeHom P ι hι hc π hπ hπ1 hD hπD⟩

end PresentedAffinoidAlgebra

end Langlands.Analytic
