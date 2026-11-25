import Langlands.LocalFactor.Ramification.ArtinExponent
import Langlands.LocalFactor.Ramification.InertiaPresentationProof

/-!
# The Artin and Swan exponents of a representation of the local Weil group

For a finite-dimensional complex representation `A` of the local Weil group of a p-adic field
`F`, the Artin and Swan exponents `artinExponent F A`, `swanExponent F A : ℕ` are the Artin and
Swan expressions of a finite inertia presentation of `A` (`Ramification.Padic.FiniteInertiaPresentation`),
and `0` when `A` has none. Every presentation gives the same values
(`Ramification.Padic.finiteInertiaConductorIndependence`), and they are natural numbers
(`Ramification.Padic.exists_nat_artinConductorOfQuotient`), so every presentation computes the
exponents (`artinExponent_eq`, `swanExponent_eq`). A continuous representation has a presentation
(`exists_presentation_of_isContinuous`). The exponents depend only on the equivalence class
(`artinExponent_eq_of_equiv`), and `a(A) = dim A − dim A^I + sw(A)` with `I` the inertia subgroup
of the Weil group (`artinExponent_eq_add_swanExponent`).
-/

noncomputable section

namespace Langlands.Weil.Local

open Module Ramification.Padic

universe uF uV uW

section Definitions

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F))

open Classical in
/-- **The Artin exponent** of a finite-dimensional complex representation of the local Weil
group: the Artin expression of a finite inertia presentation (all presentations give the same
natural number), and `0` if the representation has no presentation. -/
def artinExponent : ℕ :=
  if h : Nonempty (FiniteInertiaPresentation F A) then
    ⌊(Classical.choice h).artinConductor
      (Ramification.HerbrandBridge.weilInertiaRestriction_surjective F _)⌋₊
  else 0

open Classical in
/-- **The Swan exponent** of a finite-dimensional complex representation of the local Weil group:
the Swan expression of a finite inertia presentation, and `0` if there is none. -/
def swanExponent : ℕ :=
  if h : Nonempty (FiniteInertiaPresentation F A) then
    ⌊(Classical.choice h).swanConductor
      (Ramification.HerbrandBridge.weilInertiaRestriction_surjective F _)⌋₊
  else 0

end Definitions

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {A : FiniteRepresentation.{0, uF, uV} ℂ (localWeilGroup F)}

/-- **Every presentation computes the Artin exponent.** -/
theorem artinExponent_eq (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    (artinExponent F A : ℚ) = P.artinConductor hP := by
  have h : Nonempty (FiniteInertiaPresentation F A) := ⟨P⟩
  rw [artinExponent, dite_eq_left h]
  set Q := Classical.choice h
  have hQ := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F Q.extension
  obtain ⟨a, ha⟩ := exists_nat_artinConductorOfQuotient
    (absoluteFiniteExtension F Q.extension).canonicalTopologicalData F.Carrier _ hQ _ Q.kernel_le
  have ha' : Q.artinConductor hQ = (a : ℚ) := ha
  rw [← (finiteInertiaConductorIndependence F A Q P hQ hP).1, ha', Nat.floor_natCast]

/-- **Every presentation computes the Swan exponent.** -/
theorem swanExponent_eq (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    (swanExponent F A : ℚ) = P.swanConductor hP := by
  have h : Nonempty (FiniteInertiaPresentation F A) := ⟨P⟩
  rw [swanExponent, dite_eq_left h]
  set Q := Classical.choice h
  have hQ := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F Q.extension
  obtain ⟨s, hs⟩ := exists_nat_swanConductorOfQuotient
    (absoluteFiniteExtension F Q.extension).canonicalTopologicalData F.Carrier _ hQ _ Q.kernel_le
  have hs' : Q.swanConductor hQ = (s : ℚ) := hs
  rw [← (finiteInertiaConductorIndependence F A Q P hQ hP).2, hs', Nat.floor_natCast]

/-- Without a presentation both exponents are `0`. -/
theorem artinExponent_eq_zero_of_isEmpty (h : IsEmpty (FiniteInertiaPresentation F A)) :
    artinExponent F A = 0 := by
  rw [artinExponent, dite_eq_right (not_nonempty_iff.mpr h)]

theorem swanExponent_eq_zero_of_isEmpty (h : IsEmpty (FiniteInertiaPresentation F A)) :
    swanExponent F A = 0 := by
  rw [swanExponent, dite_eq_right (not_nonempty_iff.mpr h)]

/-- **Existence of a presentation**: a continuous representation has a finite inertia
presentation, with surjective inertia restriction, whose Artin and Swan expressions are the
exponents. -/
theorem exists_presentation_of_isContinuous (hA : A.IsContinuous) :
    ∃ (P : FiniteInertiaPresentation F A)
      (hP : Function.Surjective (weilInertiaRestriction F P.extension)),
      P.artinConductor hP = artinExponent F A ∧ P.swanConductor hP = swanExponent F A := by
  obtain ⟨P⟩ := Ramification.HerbrandBridge.continuousWeilFiniteInertiaPresentation F A hA
  have hP := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F P.extension
  exact ⟨P, hP, (artinExponent_eq P hP).symm, (swanExponent_eq P hP).symm⟩

/-- A presentation of `A` is one of every equivalent representation, on the same field. -/
def presentationOfEquiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) (P : FiniteInertiaPresentation F A) :
    FiniteInertiaPresentation F B :=
  ⟨P.extension, kernel_le_of_equiv (absoluteFiniteExtension F P.extension).canonicalTopologicalData
    F.Carrier _ P.kernel_le (localInertiaRepresentationEquiv F e)⟩

/-- **The Artin exponent depends only on the equivalence class.** -/
theorem artinExponent_eq_of_equiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : artinExponent F A = artinExponent F B := by
  by_cases h : Nonempty (FiniteInertiaPresentation F A)
  · obtain ⟨P⟩ := h
    have hP := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F P.extension
    have hB := artinExponent_eq (presentationOfEquiv e P) hP
    have hAB := (finiteInertiaConductorEquivalence F A B e P (presentationOfEquiv e P) hP hP).1
    exact_mod_cast (artinExponent_eq P hP).trans (hAB.trans hB.symm)
  · have hB : ¬Nonempty (FiniteInertiaPresentation F B) :=
      fun ⟨Q⟩ => h ⟨presentationOfEquiv e.symm Q⟩
    rw [artinExponent_eq_zero_of_isEmpty (not_nonempty_iff.mp h),
      artinExponent_eq_zero_of_isEmpty (not_nonempty_iff.mp hB)]

/-- **The Swan exponent depends only on the equivalence class.** -/
theorem swanExponent_eq_of_equiv {B : FiniteRepresentation.{0, uF, uW} ℂ (localWeilGroup F)}
    (e : FiniteRepresentation.Equiv A B) : swanExponent F A = swanExponent F B := by
  by_cases h : Nonempty (FiniteInertiaPresentation F A)
  · obtain ⟨P⟩ := h
    have hP := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F P.extension
    have hB := swanExponent_eq (presentationOfEquiv e P) hP
    have hAB := (finiteInertiaConductorEquivalence F A B e P (presentationOfEquiv e P) hP hP).2
    exact_mod_cast (swanExponent_eq P hP).trans (hAB.trans hB.symm)
  · have hB : ¬Nonempty (FiniteInertiaPresentation F B) :=
      fun ⟨Q⟩ => h ⟨presentationOfEquiv e.symm Q⟩
    rw [swanExponent_eq_zero_of_isEmpty (not_nonempty_iff.mp h),
      swanExponent_eq_zero_of_isEmpty (not_nonempty_iff.mp hB)]

/-- The vectors fixed by the inertia group of a presentation are the vectors fixed by the inertia
subgroup of the Weil group. -/
theorem fixedVectors_presentation (P : FiniteInertiaPresentation F A)
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    fixedVectors (P.representation hP) ⊤ =
      Representation.invariants (localInertiaRepresentation F A) := by
  ext v
  rw [Representation.mem_invariants]
  change (∀ g : (⊤ : Subgroup _), P.representation hP g.1 v = v) ↔ _
  constructor
  · intro h w
    have := h ⟨weilInertiaRestriction F P.extension w, Subgroup.mem_top _⟩
    rwa [P.representation_apply hP w] at this
  · intro h g
    obtain ⟨w, hw⟩ := hP g.1
    rw [← hw, P.representation_apply hP w]
    exact h w

/-- **Artin = tame + Swan**: when `A` has a presentation (for instance when it is continuous),
`a(A) = dim A − dim A^I + sw(A)`, with `A^I` the vectors fixed by the inertia subgroup of the Weil
group. -/
theorem artinExponent_eq_add_swanExponent (h : Nonempty (FiniteInertiaPresentation F A)) :
    artinExponent F A =
      (A.rank - finrank ℂ (Representation.invariants (localInertiaRepresentation F A))) +
        swanExponent F A := by
  obtain ⟨P⟩ := h
  have hP := Ramification.HerbrandBridge.weilInertiaRestriction_surjective F P.extension
  let T := (absoluteFiniteExtension F P.extension).canonicalTopologicalData
  have htame := inertiaArtinConductor_eq_tame_add_swan T F.Carrier (P.representation hP)
  have hcodim : Ramification.fixedCodimension (Ramification.Padic.inertia T F.Carrier) (P.representation hP) ⊤ =
      A.rank - finrank ℂ (Representation.invariants (localInertiaRepresentation F A)) := by
    rw [Ramification.fixedCodimension, fixedVectors_presentation P hP]
    rfl
  have ha : (artinExponent F A : ℚ) = inertiaArtinConductor T F.Carrier (P.representation hP) :=
    artinExponent_eq P hP
  have hs : (swanExponent F A : ℚ) = inertiaSwanConductor T F.Carrier (P.representation hP) :=
    swanExponent_eq P hP
  rw [← ha, ← hs, hcodim] at htame
  exact_mod_cast htame

end Langlands.Weil.Local
