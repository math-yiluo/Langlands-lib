import Langlands.AlgebraicGeometry.DvrSmoothening.Points

/-! # Centres of the smoothening: closures of closed points of non-smooth points -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation f]

/-- The closed points of the points of `E` which do not lie in the smooth locus. -/
def badSet (E : TestPoint X f → Prop) : Set X :=
  {x | ∃ P, E P ∧ P.special ∉ f.smoothLocus ∧ P.special = x}

/-- The closure of `badSet f E`. -/
def centre (E : TestPoint X f → Prop) : Closeds X := ⟨closure (badSet f E), isClosed_closure⟩

theorem mem_badSet {E : TestPoint X f → Prop} {P : TestPoint X f} (hP : E P)
    (hs : P.special ∉ f.smoothLocus) : P.special ∈ centre f E :=
  subset_closure ⟨P, hP, hs, rfl⟩

theorem centre_special (E : TestPoint X f → Prop) {x : X} (hx : x ∈ centre f E) :
    f x = IsLocalRing.closedPoint R := by
  have hcl : IsClosed (f ⁻¹' {IsLocalRing.closedPoint R}) :=
    (IsLocalRing.isClosed_singleton_closedPoint R).preimage f.continuous
  have : badSet f E ⊆ f ⁻¹' {IsLocalRing.closedPoint R} := by
    rintro _ ⟨P, -, -, rfl⟩
    exact P.f_special
  exact (closure_minimal this hcl) hx

theorem centre_nonsmooth (E : TestPoint X f → Prop) {x : X} (hx : x ∈ centre f E) :
    x ∉ f.smoothLocus := by
  have hcl : IsClosed ((f.smoothLocus : Set X)ᶜ) := f.smoothLocus.2.isClosed_compl
  have : badSet f E ⊆ (f.smoothLocus : Set X)ᶜ := by
    rintro _ ⟨P, -, hs, rfl⟩
    exact hs
  exact (closure_minimal this hcl) hx

theorem not_mem_centre_of_generic (E : TestPoint X f → Prop) {x : X}
    (hx : (f x).asIdeal = ⊥) : x ∉ centre f E := by
  intro hc
  have h := centre_special f E hc
  rw [h] at hx
  exact IsDiscreteValuationRing.not_a_field R hx

theorem centre_mono {E E' : TestPoint X f → Prop} (h : ∀ P, E P → E' P) :
    centre f E ≤ centre f E' := by
  apply closure_mono
  rintro _ ⟨P, hP, hs, rfl⟩
  exact ⟨P, h P hP, hs, rfl⟩

/-- The vanishing ideal of the centre in a chart is the intersection of the primes of the closed
points of the non-smooth points through the chart. -/
theorem vanishingIdeal_centre (E : TestPoint X f → Prop) (C : AffineChart X) :
    PrimeSpectrum.vanishingIdeal (C.ι ⁻¹' (centre f E)) =
      sInf {q : Ideal C.ring | ∃ P, E P ∧ P.special ∉ f.smoothLocus ∧
        ∃ h : P.special ∈ C.ι.opensRange,
          q = (IsLocalRing.maximalIdeal P.ring).comap (C.pointHom P.a h)} := by
  have hpre : (C.ι ⁻¹' (centre f E : Set X) : Set (PrimeSpectrum C.ring)) =
      closure (C.ι ⁻¹' badSet f E : Set (PrimeSpectrum C.ring)) :=
    C.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage C.ι.continuous _
  rw [hpre, PrimeSpectrum.vanishingIdeal_closure]
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨P, hP, hs, h, rfl⟩
    refine le_trans (iInf₂_le (C.liftPoint P.a h (IsLocalRing.closedPoint P.ring)) ?_)
      (le_of_eq (C.liftPoint_closedPoint P.a h))
    exact ⟨P, hP, hs, (C.ι_liftPoint_closedPoint P.a h).symm⟩
  · apply le_iInf₂
    rintro p ⟨P, hP, hs, hp⟩
    have h : P.special ∈ C.ι.opensRange := ⟨p, hp.symm⟩
    have hpe : p = C.liftPoint P.a h (IsLocalRing.closedPoint P.ring) := by
      apply C.ι.isOpenEmbedding.injective
      exact hp.symm.trans (C.ι_liftPoint_closedPoint P.a h).symm
    apply sInf_le
    refine ⟨P, hP, hs, h, ?_⟩
    rw [hpe]
    exact C.liftPoint_closedPoint P.a h

end Langlands.AlgebraicGeometry.DvrSmoothening
