import Langlands.Representation.Geometric.CompactOrbitRestriction
import Langlands.Representation.Geometric.OrbitSectionExtensionProof
import Langlands.Representation.Filtration.QuotientFirstIso

/-! Actual orbit restriction for any adjacent pair of open invariant supports. -/

noncomputable section
open CategoryTheory

namespace Langlands.Geometric

universe uR uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Two open invariant supports whose actual set difference is a specified orbit.
No enumeration of the other orbits is part of the data. -/
structure OpenOrbitSupportPair (P Q : Subgroup G) (w : G) where
  lower : Set (Induction.LeftQuotient P)
  upper : Set (Induction.LeftQuotient P)
  lower_invariant : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ lower →
    Induction.quotientRight P (q : G) x ∈ lower
  upper_invariant : ∀ (q : Q) (x : Induction.LeftQuotient P), x ∈ upper →
    Induction.quotientRight P (q : G) x ∈ upper
  lower_open : IsOpen lower
  upper_open : IsOpen upper
  lower_subset_upper : lower ⊆ upper
  difference : upper \ lower = cosetOrbit P Q w

namespace OpenOrbitSupportPair

variable {P Q : Subgroup G} {w : G} (s : OpenOrbitSupportPair P Q w)

/-- The single new orbit belongs to the upper support. -/
theorem orbit_subset_upper : cosetOrbit P Q w ⊆ s.upper := by
  rw [← s.difference]
  exact Set.sdiff_subset

include s in
/-- The new orbit is locally closed in the actual inducing quotient. -/
theorem orbit_isLocallyClosed : IsLocallyClosed (cosetOrbit P Q w) := by
  rw [← s.difference]
  exact ⟨s.upper, s.lowerᶜ, s.upper_open, s.lower_open.isClosed_compl, rfl⟩

/-- The new orbit is relatively closed in the upper support. -/
theorem orbit_isClosed_in_upper :
    IsClosed ((fun x : s.upper => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w) := by
  have heq : ((fun x : s.upper => (x : Induction.LeftQuotient P)) ⁻¹'
      cosetOrbit P Q w) =
      ((fun x : s.upper => (x : Induction.LeftQuotient P)) ⁻¹' s.lower)ᶜ := by
    rw [← s.difference]
    ext x
    exact and_iff_right x.property
  rw [heq]
  exact (s.lower_open.preimage continuous_subtype_val).isClosed_compl

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]

/-- Vanishing on the orbit is equivalent to support in the lower open set. -/
theorem restriction_zero_iff_lower (σ : Representation R P V)
    (f : Induction.SmoothFunctions P σ)
    (hf : ∀ x : G, Induction.eval P σ f x ≠ 0 →
      Induction.quotientMap P x ∈ s.upper) :
    (∀ q : Q, Induction.eval P σ f (w⁻¹ * (q : G)) = 0) ↔
      ∀ x : G, Induction.eval P σ f x ≠ 0 →
        Induction.quotientMap P x ∈ s.lower := by
  constructor
  · intro hzero x hx
    by_contra hprev
    have horb : Induction.quotientMap P x ∈ cosetOrbit P Q w := by
      rw [← s.difference]
      exact ⟨hf x hx, hprev⟩
    obtain ⟨q, hq⟩ := horb
    exact hx (eval_eq_zero_of_quotientMap_eq P σ f hq.symm (hzero q))
  · intro hprev q
    by_contra hq
    have horb : Induction.quotientMap P (w⁻¹ * (q : G)) ∈ cosetOrbit P Q w :=
      ⟨q, rfl⟩
    rw [← s.difference] at horb
    exact horb.2 (hprev _ hq)

variable [LocallyCompactSpace G] [SigmaCompactSpace G]
  (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))

section Restriction

variable [IsTopologicalGroup G]

/-- Restriction of actual compact sections on the upper support to the orbit. -/
def restriction :
    (supportSubfunctor.{uR, uG, uV} (R := R) P Q s.upper s.upper_invariant).toFunctor ⟶
      orbitPiece P Q w :=
  supportOrbitRestrictionNat P Q w
    (cosetOrbitHomeomorph P Q w hP hQ s.orbit_isLocallyClosed)
    (cosetOrbitHomeomorph_mk P Q w hP hQ s.orbit_isLocallyClosed)
    s.upper s.upper_invariant s.orbit_isClosed_in_upper

/-- The kernel is the actual pulled-back lower support subrepresentation. -/
theorem restriction_kernel (A : Induction.SmoothRep.{uR, uG, uV} R P)
    (f : (supportSubfunctor (R := R) P Q s.upper s.upper_invariant).representation A) :
    f ∈ (supportSubfunctor (R := R) P Q s.lower s.lower_invariant).lowerInUpper
        (supportSubfunctor (R := R) P Q s.upper s.upper_invariant) A ↔
      ((s.restriction hP hQ).app A).hom f = 0 := by
  change (∀ x : G, Induction.eval P A.obj.ρ f.val.val x ≠ 0 →
    Induction.quotientMap P x ∈ s.lower) ↔ _
  rw [← s.restriction_zero_iff_lower A.obj.ρ f.val.val f.property]
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext q
    exact h q
  · intro h q
    exact congrArg (fun g : Induction.CompactFunctions (orbitStabilizer P Q w)
      (A.obj.ρ.comp (stabilizerToInducing P Q w)) => Induction.eval _ _ g.val q) h

end Restriction

section Complex

variable [NonarchimedeanGroup G] [T2Space G]

/-- The proved compact orbit-section extension gives surjectivity. -/
theorem restriction_surjective (A : Induction.SmoothRep.{0, uG, uV} ℂ P) :
    Function.Surjective ((s.restriction (R := ℂ) hP hQ).app A).hom := by
  intro g
  obtain ⟨f, hf, hfg⟩ := closedOrbitSectionExtension G P Q hP hQ w
    s.upper s.upper_open s.orbit_subset_upper s.orbit_isClosed_in_upper A g
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  exact hfg q

/-- The actual quotient between these supports is naturally the actual orbit piece. -/
def quotientIso :
    (supportSubfunctor.{0, uG, uV} (R := ℂ) P Q s.lower s.lower_invariant).quotientFunctor
      (supportSubfunctor (R := ℂ) P Q s.upper s.upper_invariant) ≅
        orbitPiece P Q w :=
  (supportSubfunctor (R := ℂ) P Q s.lower s.lower_invariant).quotientNatIsoOfSurjective
    (supportSubfunctor (R := ℂ) P Q s.upper s.upper_invariant)
    (s.restriction hP hQ) (s.restriction_kernel hP hQ)
    (s.restriction_surjective hP hQ)

/-- The isomorphism is actual restriction on every upper-support representative. -/
@[simp]
theorem quotientIso_hom_projection (A : Induction.SmoothRep.{0, uG, uV} ℂ P)
    (f : (supportSubfunctor (R := ℂ) P Q s.upper s.upper_invariant).representation A) :
    ((s.quotientIso hP hQ).hom.app A).hom
      (((supportSubfunctor (R := ℂ) P Q s.lower s.lower_invariant).quotientProjection
        (supportSubfunctor (R := ℂ) P Q s.upper s.upper_invariant) A).hom f) =
      ((s.restriction hP hQ).app A).hom f := rfl

end Complex
end OpenOrbitSupportPair
end Langlands.Geometric
