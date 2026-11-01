import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartTerminal
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartIntersection
import Langlands.Geometry.Analytic.Spectrum.LaurentNeighborhoods

/-! # Actual positive-radius rational charts for finite Laurent neighborhoods -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {A : PresentedAffinoidAlgebra K}

private def representative (a : A) : GeneralizedTateAlgebra A.polyradius K :=
  (presentationMap_surjective K A a).choose

private theorem representative_class (a : A) :
    presentationMap K A (representative a) = a :=
  (presentationMap_surjective K A a).choose_spec

/-- The elementary positive-radius Weierstrass chart for an actual element
of the quotient presentation, with a chosen series representative. -/
def upperBound (a : A) (r : ℝ) (hr : 0 < r) : RationalChart K A where
  arity := 1
  radii := ⟨fun _ => r, fun _ => hr⟩
  denominator := 1
  numerators _ := representative a
  generates := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    left
    exact (map_one (presentationMap K A).toAlgHom).symm

@[simp] theorem mem_locus_upperBound (a : A) (r : ℝ) (hr : 0 < r)
    (x : BanachSpectrum A) :
    x ∈ (upperBound a r hr).locus ↔ x a ≤ r := by
  simp [upperBound, locus, RationalPresentation.locus, representative_class]

/-- The elementary positive-radius Laurent chart imposing a positive lower
bound. Its unit numerator makes unit generation unconditional. -/
def lowerBound (a : A) (q : ℝ) (hq : 0 < q) : RationalChart K A where
  arity := 1
  radii := ⟨fun _ => q⁻¹, fun _ => inv_pos.mpr hq⟩
  denominator := representative a
  numerators _ := 1
  generates := by
    apply (Ideal.eq_top_iff_one _).mpr
    apply Ideal.subset_span
    right
    exact ⟨0, map_one (presentationMap K A).toAlgHom⟩

@[simp] theorem mem_locus_lowerBound (a : A) (q : ℝ) (hq : 0 < q)
    (x : BanachSpectrum A) :
    x ∈ (lowerBound a q hq).locus ↔ q ≤ x a := by
  simp only [lowerBound, locus, RationalPresentation.locus, representative_class,
    map_one]
  simp only [Fin.forall_fin_one]
  change 1 ≤ q⁻¹ * x a ↔ q ≤ x a
  rw [← div_eq_inv_mul, le_div_iff₀ hq, one_mul]

/-- Iterate the existing all-products intersection presentation. -/
def listInter : List (RationalChart K A) → RationalChart K A
  | [] => whole K A
  | d :: ds => d.inter (listInter ds)

@[simp] theorem mem_locus_listInter (ds : List (RationalChart K A))
    (x : BanachSpectrum A) : x ∈ (listInter ds).locus ↔ ∀ d ∈ ds, x ∈ d.locus := by
  induction ds with
  | nil => simp [listInter]
  | cons d ds ih => simp [listInter, ih]

/-- Intersect a finite family of actual charts, allowing the empty family. -/
def finiteInter {I : Type v} [Fintype I] (D : I → RationalChart K A) :
    RationalChart K A :=
  listInter (Finset.univ.toList.map D)

@[simp] theorem mem_locus_finiteInter {I : Type v} [Fintype I]
    (D : I → RationalChart K A) (x : BanachSpectrum A) :
    x ∈ (finiteInter D).locus ↔ ∀ i, x ∈ (D i).locus := by
  simp [finiteInter]

/-- An actual ambient rational chart for arbitrary finite positive-threshold
Laurent inequalities in quotient elements. -/
def finiteLaurent (s t : Finset A) (r : s → ℝ) (q : t → ℝ)
    (hr : ∀ i, 0 < r i) (hq : ∀ j, 0 < q j) : RationalChart K A :=
  (finiteInter (fun i : s => upperBound i.val (r i) (hr i))).inter
    (finiteInter (fun j : t => lowerBound j.val (q j) (hq j)))

@[simp] theorem locus_finiteLaurent (s t : Finset A) (r : s → ℝ) (q : t → ℝ)
    (hr : ∀ i, 0 < r i) (hq : ∀ j, 0 < q j) :
    (finiteLaurent s t r q hr hq).locus =
      BanachSpectrum.laurentLocus (fun i : s => i.val) r (fun j : t => j.val) q := by
  ext x
  simp [finiteLaurent, BanachSpectrum.laurentLocus]

/-- Every neighborhood of a base spectrum point contains the locus of an
actual ambient rational chart that is itself a neighborhood of the point. -/
theorem exists_rational_neighborhood (x : BanachSpectrum A)
    (V : Set (BanachSpectrum A)) (hV : V ∈ 𝓝 x) :
    ∃ d : RationalChart K A, d.locus ∈ 𝓝 x ∧ d.locus ⊆ V := by
  obtain ⟨s, t, r, q, hr, hq, _, _, hx, hsub⟩ :=
    BanachSpectrum.exists_finite_laurent_neighborhood x V hV
  refine ⟨finiteLaurent s t r q hr hq, ?_, ?_⟩
  · rw [locus_finiteLaurent]
    exact mem_interior_iff_mem_nhds.mp hx
  · rwa [locus_finiteLaurent]

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
