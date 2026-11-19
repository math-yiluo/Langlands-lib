import Langlands.Geometry.Analytic.AffineAnalytificationCenterSurjectivityProof
import Langlands.Geometry.Analytic.AffineAnalytificationSeminormProof
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Maximal centers of affine analytifications -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- A maximal ideal of a finite-type algebra is the center of an analytic point,
obtained by pulling back the norm on its finite residue field. -/
def maximalCenterLift (m : Ideal A) [m.IsMaximal] :
    {x : Space K P // (center K P x).asIdeal = m} := by
  let p : PrimeSpectrum A := ⟨m, inferInstance⟩
  let : Algebra.FiniteType K A := Algebra.FiniteType.of_surjective P.map P.surjective
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K _
  let n := spectralMulAlgNorm K (A ⧸ m)
  have hn : ExtendsNorm K n.toMulRingNorm.toMulRingSeminorm :=
    fun k => spectralNorm_extends k
  have hν := CenterSurjectivity.exists_seminorm_with_kernel K p
    n.toMulRingNorm.toMulRingSeminorm hn
    (fun _ h => (map_eq_zero_iff_eq_zero n).mp h)
  let ν := hν.choose
  have hx : ν ∈ Set.range (pointSeminorm K P) := by
    rw [SeminormComparison.range_pointSeminorm]
    exact hν.choose_spec.1
  refine ⟨hx.choose, ?_⟩
  ext a
  rw [center_asIdeal, mem_kernel, hx.choose_spec]
  exact hν.choose_spec.2 a

variable {B : Type w} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)

/-- A flat affine algebra map that is surjective on analytic points is faithfully flat. -/
theorem faithfullyFlat_of_flat_of_baseMap_surjective
    (f : A →ₐ[K] B) (hf : f.toRingHom.Flat)
    (h : Function.Surjective (baseMap K P Q f)) : f.toRingHom.FaithfullyFlat := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Module.Flat A B := hf
  refine ⟨?_⟩
  intro m hm
  let : m.IsMaximal := hm
  let x := maximalCenterLift K P m
  obtain ⟨y, hy⟩ := h x.val
  have he : (center K Q y).asIdeal.comap (algebraMap A B) = m := by
    change (PrimeSpectrum.comap (f : A →+* B) (center K Q y)).asIdeal = m
    rw [← center_baseMap K P Q f, hy]
    exact x.property
  rw [Ideal.smul_top_eq_map, ← he]
  exact (Submodule.restrictScalars_eq_top_iff A B B).ne.mpr
    fun ht => (center K Q y).isPrime.ne_top (top_le_iff.mp (ht ▸ Ideal.map_comap_le))

/-- A flat algebra quotient that is surjective on analytic points is bijective. -/
theorem bijective_of_surjective_of_flat_of_baseMap_surjective
    (f : A →ₐ[K] B) (hs : Function.Surjective f) (hf : f.toRingHom.Flat)
    (h : Function.Surjective (baseMap K P Q f)) : Function.Bijective f :=
  ⟨(faithfullyFlat_of_flat_of_baseMap_surjective K P Q f hf h).injective, hs⟩

end Langlands.Analytic.AffineAnalytification
