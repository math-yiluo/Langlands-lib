import Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeProof
import Langlands.Geometry.Analytic.AffineAnalytificationChartFlatProof
import Langlands.Geometry.Analytic.AffineAnalytificationMaximalCenters
import Langlands.Geometry.Analytic.FiniteMorphismFibres
import Mathlib.RingTheory.HopkinsLevitzki

/-! # Affine analytification of finite local algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffineAnalytification

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {D : Type v} [CommRing D] [Algebra K D] [IsLocalRing D]
  (P : FinitePolynomialPresentation K D)

/-- A local algebra with a finite polynomial presentation has an analytic point. -/
theorem nonempty_space_of_isLocalRing : Nonempty (Space K P) :=
  ⟨(maximalCenterLift K P (IsLocalRing.maximalIdeal D)).val⟩

variable [Module.Finite K D]

private theorem pointSeminorm_eq_spectralNorm_residue (x : Space K P) (a : D) :
    pointSeminorm K P x a =
      spectralNorm K (IsLocalRing.ResidueField D) (IsLocalRing.residue D a) := by
  obtain ⟨L, _, _, _, _, ρ, hρ⟩ :=
    BaseChangeComparison.normedRealization (pointSeminorm K P x) (pointSeminorm_extendsNorm K P x)
  let : IsArtinianRing D := IsArtinianRing.of_finite K D
  have hker : RingHom.ker ρ.toRingHom = IsLocalRing.maximalIdeal D := by
    let : (RingHom.ker ρ.toRingHom).IsPrime := RingHom.ker_isPrime ρ.toRingHom
    exact Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _
  let E := IsLocalRing.ResidueField D
  let q : D →ₐ[K] E := Ideal.Quotient.mkₐ K _
  let : Module.Finite K E := Module.Finite.of_surjective q.toLinearMap Ideal.Quotient.mk_surjective
  let ι : E →ₐ[K] L := Ideal.Quotient.liftₐ _ ρ (fun _ h => hker.ge h)
  rw [← hρ]
  change ‖ι (q a)‖ = spectralNorm K E (q a)
  exact spectralNorm_unique_field_norm_ext (f := pullbackAbsoluteValue ι.toRingHom)
    (fun k => by change ‖ι (algebraMap K E k)‖ = ‖k‖; rw [ι.commutes, norm_algebraMap']) _

/-- The analytification of a finite local algebra has at most one point. -/
theorem subsingleton_space_of_finite_of_isLocalRing : Subsingleton (Space K P) :=
  ⟨fun x y => SeminormComparison.pointSeminorm_injective K P (by
    ext a
    rw [pointSeminorm_eq_spectralNorm_residue K P x, pointSeminorm_eq_spectralNorm_residue K P y])⟩

/-- A nonempty chart of the analytification of a finite local algebra
has the original coordinate algebra. -/
def finiteLocalChartEquiv (i : (presentation K P).atlas.Index)
    (hi : Nonempty (BanachSpectrum ((presentation K P).atlas.algebra i))) :
    D ≃ₐ[K] (presentation K P).atlas.algebra i := by
  let R := (presentation K P).atlas.algebra i
  let α : D →ₐ[K] R := chartAlgebraMap K P i
  refine AlgEquiv.ofBijective α ⟨?_, ?_⟩
  · obtain ⟨s⟩ := hi
    let : Nontrivial R := nontrivial_of_ne (1 : R) 0 fun h =>
      one_ne_zero (by simpa only [map_one, map_zero] using congrArg s.toMulRingSeminorm h)
    let : IsArtinianRing D := IsArtinianRing.of_finite K D
    let : Subsingleton (PrimeSpectrum D) := Ring.KrullDimLE.subsingleton_primeSpectrum D
    have hflat : α.toRingHom.Flat := ChartFlatness.flat_chartAlgebraMap K P i.val
    have hsurj : Function.Surjective (PrimeSpectrum.comap α.toRingHom) :=
      fun _ => ⟨Classical.choice inferInstance, Subsingleton.elim _ _⟩
    exact ((RingHom.FaithfullyFlat.iff_flat_and_comap_surjective).2 ⟨hflat, hsurj⟩).injective
  · have hd : DenseRange α := SeminormComparison.denseRange_chartAlgebraMap K P i.val
    have hc : IsClosed (Set.range α) := by
      change IsClosed (Set.range α.toLinearMap)
      rw [← LinearMap.coe_range]
      exact Submodule.closed_of_finiteDimensional _
    intro r
    change r ∈ Set.range α
    rw [← hc.closure_eq]
    exact hd r

@[simp]
theorem finiteLocalChartEquiv_toAlgHom (i : (presentation K P).atlas.Index)
    (hi : Nonempty (BanachSpectrum ((presentation K P).atlas.algebra i))) :
    (finiteLocalChartEquiv K P i hi).toAlgHom = chartAlgebraMap K P i := rfl

end Langlands.Analytic.AffineAnalytification
