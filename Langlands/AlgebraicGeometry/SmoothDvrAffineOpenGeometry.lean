import Langlands.AlgebraicGeometry.FibrewiseClopenAffineOpen
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing
import Langlands.AnthropicFLT.Theorems.Thm_IsRegularLocalRing_isDomain
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Affineness of fibrewise closed opens in smooth affine DVR schemes -/

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry

lemma point_eq_generic_or_closed (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (p : PrimeSpectrum R) :
    p = ⟨⊥, inferInstance⟩ ∨ p = IsLocalRing.closedPoint R := by
  by_cases hp : p.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hp)
  · right
    obtain ⟨P, hP, huniq⟩ :=
      ((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime R).mp inferInstance).2
    exact PrimeSpectrum.ext ((huniq p.asIdeal ⟨hp, p.isPrime⟩).trans
      (huniq (IsLocalRing.maximalIdeal R)
        ⟨IsDiscreteValuationRing.not_a_field R, inferInstance⟩).symm)

lemma basicOpen_eq_generic (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π) :
    (PrimeSpectrum.basicOpen π : Set (PrimeSpectrum R)) = {⟨⊥, inferInstance⟩} := by
  ext p
  rcases point_eq_generic_or_closed R p with rfl | rfl
  · simp [hπ.ne_zero]
  · have hmem : π ∈ IsLocalRing.maximalIdeal R := by
      rw [hπ.maximalIdeal_eq]
      exact Ideal.subset_span (Set.mem_singleton π)
    have hne : IsLocalRing.closedPoint R ≠ (⟨⊥, inferInstance⟩ : PrimeSpectrum R) := by
      intro heq
      exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal heq)
    simpa [PrimeSpectrum.mem_basicOpen, IsLocalRing.closedPoint, hmem] using hne

/-- An open subset of a smooth affine DVR scheme that is closed in each
underlying fibre is affine. -/
theorem isAffineOpen_of_fiberwise_closed
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (U : X.Opens)
    (hclosed : ∀ s : Spec (CommRingCat.of R),
      IsClosed ((Subtype.val : (f ⁻¹' {s}) → X) ⁻¹' (U : Set X))) :
    IsAffineOpen U := by
  classical
  let η : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  let z : PrimeSpectrum R := IsLocalRing.closedPoint R
  have hne : z ≠ η := by
    intro heq
    exact IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal heq)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let a : Γ(X, ⊤) := f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv π)
  have hD : (X.basicOpen a : Set X) = f ⁻¹' {η} := by
    change (X.basicOpen (f.appTop _) : Set X) = _
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    exact congrArg (fun Z : Set (PrimeSpectrum R) => f ⁻¹' Z)
      (basicOpen_eq_generic R hπ)
  have hbase : Dense ({η} : Set (PrimeSpectrum R)) := by
    rw [← basicOpen_eq_generic R hπ]
    apply (PrimeSpectrum.basicOpen π).isOpen.dense
    refine ⟨η, ?_⟩
    change π ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using hπ.ne_zero
  have hdense : Dense (X.basicOpen a : Set X) := by
    rw [hD]
    exact hbase.preimage f.isOpenMap
  have hlocal (x : X) : ∃ N : X.Opens, x ∈ N ∧ IsIrreducible (N : Set X) := by
    have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have : IsRegularLocalRing (X.presheaf.stalk x) :=
      Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R f x
    exact Langlands.AlgebraicGeometry.exists_irreducible_open X x hN (IsRegularLocalRing.isDomain _)
  have hgeneric : IsClosed
      ((Subtype.val : X.basicOpen a → X) ⁻¹' (U : Set X)) := by
    exact (hclosed η).preimage (Homeomorph.setCongr hD).continuous
  have hcomp : (f ⁻¹' {z} : Set X) = (X.basicOpen a : Set X)ᶜ := by
    rw [hD]
    ext x
    change f x = z ↔ f x ≠ η
    constructor
    · intro hx
      exact hx ▸ hne
    · intro hx
      exact (point_eq_generic_or_closed R (f x)).resolve_left hx
  have hspecial : IsClosed ((U : Set X) \ (X.basicOpen a : Set X)) := by
    have hz : IsClosed (f ⁻¹' {z}) :=
      (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
    have himage := hz.isClosedEmbedding_subtypeVal.isClosedMap _ (hclosed z)
    have heq : (Subtype.val : (f ⁻¹' {z}) → X) ''
        ((Subtype.val : (f ⁻¹' {z}) → X) ⁻¹' (U : Set X)) =
        (U : Set X) \ (X.basicOpen a : Set X) := by
      rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype, hcomp]
      rfl
    exact heq ▸ himage
  exact FibrewiseClopenAffineOpen.isAffineOpen_of_closed_on_principal_and_complement
    X a U hlocal hdense hgeneric hspecial

end Langlands.AlgebraicGeometry.SmoothDvrAffineOpenGeometry
