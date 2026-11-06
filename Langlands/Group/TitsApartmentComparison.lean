import Langlands.Group.TitsParabolicRigidity
import Langlands.Group.TitsSystemRestricted
import Langlands.Group.RelativeWeylConjugation

/-! # Apartment comparison in a restricted Tits building -/

namespace Langlands.Group

open TitsSystem RelativeWeyl

variable {G W : Type*} [Group G] [Group W]
  {B N : Subgroup G} {π : N →* W} {S : Set W}

namespace IsTitsSystem

variable (h : IsTitsSystem B N π S)
include h

/-- Double-coset equality of normalizer representatives can be realized with
a normalizer element on the left which belongs to the left parabolic. -/
theorem exists_normalizer_doubleCoset_factor
    {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    (n m : N)
    (hnm : DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q (m : G)) :
    ∃ r : N, (r : G) ∈ P ∧ (m : G)⁻¹ * r * n ∈ Q := by
  obtain ⟨X, hX, hP⟩ := h.exists_eq_standardParabolic P hBP
  obtain ⟨Y, hY, hQ⟩ := h.exists_eq_standardParabolic Q hBQ
  obtain ⟨e, he⟩ := h.exists_doubleCoset_equiv hX hY rfl rfl hP hQ
  have hnmW : DoubleCoset.mk (Subgroup.closure X) (Subgroup.closure Y) (π n) =
      DoubleCoset.mk (Subgroup.closure X) (Subgroup.closure Y) (π m) := by
    apply e.injective
    simpa only [he] using hnm
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.eq.mp hnmW
  obtain ⟨r, hr⟩ := h.surjective x
  refine ⟨r, rep_mem_of_coe_eq hP (hr ▸ hx), ?_⟩
  apply rep_mem_of_coe_eq hQ (n := m⁻¹ * r * n)
  have heq : π (m⁻¹ * r * n) = y⁻¹ := by
    simp [hxy, hr, mul_assoc]
  rw [heq]
  exact (Subgroup.closure Y).inv_mem hy

/-- Adjust an apartment representative in `P` by a normalizer element so that
it also belongs to the conjugate `n Q n⁻¹`. -/
theorem exists_normalizer_mem_two_parabolics
    {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    {g : G} (hg : g ∈ P) (n m : N)
    (hmgn : (m : G)⁻¹ * g⁻¹ * n ∈ Q) :
    ∃ r : N, g * r ∈ P ∧ (n : G)⁻¹ * (g * r) * n ∈ Q := by
  have hnm : DoubleCoset.mk P Q (n : G) = DoubleCoset.mk P Q (m : G) := by
    symm
    exact DoubleCoset.eq.mpr ⟨g, hg, (m : G)⁻¹ * g⁻¹ * n, hmgn,
      by simp [mul_assoc]⟩
  obtain ⟨r, hrP, hrQ⟩ := h.exists_normalizer_doubleCoset_factor hBP hBQ n m hnm
  refine ⟨r, P.mul_mem hg hrP, ?_⟩
  simpa [mul_assoc] using Q.mul_mem (Q.inv_mem hmgn) hrQ

/-- A standard parabolic conjugate is the underlying set of the corresponding
actual conjugate subgroup. -/
theorem coe_conjugate_standardParabolic {X : Set W} (hX : X ⊆ S) (g : G) :
    (conjugateSubgroup g (h.standardParabolicSubgroup hX) : Set G) =
      conjStandardParabolic B π g X :=
  rfl

/-- Subgroup form of membership in a restricted apartment. -/
theorem mem_restrictedApartment_iff_conjugate {g : G} {P : Subgroup G} :
    P ∈ restrictedApartment B π S g ↔
      ∃ (n : N) (X : Set W) (hX : IsAdmissibleType S X),
        P = conjugateSubgroup (g * n) (h.standardParabolicSubgroup hX.1) := by
  constructor
  · rintro ⟨n, X, hX, hP⟩
    exact ⟨n, X, hX, SetLike.coe_injective hP⟩
  · rintro ⟨n, X, hX, rfl⟩
    exact ⟨n, X, hX, rfl⟩

/-- Right multiplication by the normalizer preserves a restricted apartment. -/
theorem restrictedApartment_mul_normalizer (g : G) (n : N) :
    restrictedApartment B π S (g * n) = restrictedApartment B π S g := by
  ext P
  simp only [h.mem_restrictedApartment_iff_conjugate]
  constructor
  · rintro ⟨m, X, hX, rfl⟩
    exact ⟨n * m, X, hX, by simp [mul_assoc]⟩
  · rintro ⟨m, X, hX, rfl⟩
    exact ⟨n⁻¹ * m, X, hX, by simp [mul_assoc]⟩

/-- Conjugation carries a restricted apartment to the translated apartment. -/
theorem image_conjugateSubgroup_restrictedApartment (g a : G) :
    conjugateSubgroup g '' restrictedApartment B π S a =
      restrictedApartment B π S (g * a) := by
  ext P
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨n, X, hX, rfl⟩ := h.mem_restrictedApartment_iff_conjugate.mp hQ
    apply h.mem_restrictedApartment_iff_conjugate.mpr
    exact ⟨n, X, hX, by rw [← conjugateSubgroup_mul, mul_assoc]⟩
  · intro hP
    obtain ⟨n, X, hX, rfl⟩ := h.mem_restrictedApartment_iff_conjugate.mp hP
    refine ⟨conjugateSubgroup (a * n) (h.standardParabolicSubgroup hX.1),
      h.mem_restrictedApartment_iff_conjugate.mpr ⟨n, X, hX, rfl⟩, ?_⟩
    rw [← conjugateSubgroup_mul, mul_assoc]

/-- If two standard overgroups of `B` are conjugate, the conjugator belongs
to the target overgroup. -/
theorem mem_of_eq_conjugate {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    {g : G} (heq : P = conjugateSubgroup g Q) : g ∈ P := by
  apply P.inv_mem_iff.mp
  apply h.mem_of_conjugate_le hBP g⁻¹
  intro b hb
  rw [heq]
  exact ⟨b, hBQ hb, by simp⟩

/-- The Tits-system apartment comparison for a standard parabolic and a
normalizer conjugate of another standard parabolic (KP Proposition 1.5.6(5)).
The transporter belongs to both parabolics, so it fixes every parabolic
containing either one under conjugation. -/
theorem exists_mem_two_parabolics_restrictedApartment_eq
    {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    (n : N) (g : G)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : conjugateSubgroup (n : G) Q ∈ restrictedApartment B π S g) :
    ∃ k : G, k ∈ P ∧ k ∈ conjugateSubgroup (n : G) Q ∧
      restrictedApartment B π S k = restrictedApartment B π S g := by
  obtain ⟨m₀, X, hX, hP⟩ := h.mem_restrictedApartment_iff_conjugate.mp hPg
  let t : G := g * m₀
  have htP : t ∈ P :=
    h.mem_of_eq_conjugate hBP (h.le_of_coe_eq rfl) hP
  have hAt : restrictedApartment B π S t = restrictedApartment B π S g :=
    h.restrictedApartment_mul_normalizer g m₀
  rw [← hAt] at hQg
  obtain ⟨m, Y, hY, hQ⟩ := h.mem_restrictedApartment_iff_conjugate.mp hQg
  have hQ' : Q = conjugateSubgroup ((n : G)⁻¹ * (t * m))
      (h.standardParabolicSubgroup hY.1) := by
    have heq := congrArg (conjugateSubgroup (n : G)⁻¹) hQ
    simpa only [← conjugateSubgroup_mul, inv_mul_cancel,
      conjugateSubgroup_one] using heq
  have hq : (m : G)⁻¹ * t⁻¹ * n ∈ Q := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using
      Q.inv_mem (h.mem_of_eq_conjugate hBQ (h.le_of_coe_eq rfl) hQ')
  obtain ⟨r, htrP, htrQ⟩ := h.exists_normalizer_mem_two_parabolics hBP hBQ htP n m hq
  refine ⟨t * r, htrP, ?_, (h.restrictedApartment_mul_normalizer t r).trans hAt⟩
  exact ⟨(n : G)⁻¹ * (t * r) * n, htrQ, by simp [mul_assoc]⟩

/-- A chosen transporter in both parabolics representing the specified
restricted apartment. Its existence is derived from the Tits-system axioms. -/
noncomputable def twoParabolicApartmentTransport
    {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    (n : N) (g : G)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : conjugateSubgroup (n : G) Q ∈ restrictedApartment B π S g) :
    ↥(P ⊓ conjugateSubgroup (n : G) Q) :=
  ⟨(h.exists_mem_two_parabolics_restrictedApartment_eq hBP hBQ n g hPg hQg).choose,
    (h.exists_mem_two_parabolics_restrictedApartment_eq hBP hBQ n g hPg hQg).choose_spec.1,
    (h.exists_mem_two_parabolics_restrictedApartment_eq hBP hBQ n g hPg hQg).choose_spec.2.1⟩

/-- The chosen transporter carries the standard restricted apartment to the
specified apartment, in the parabolic-subgroup description. -/
theorem restrictedApartment_twoParabolicApartmentTransport
    {P Q : Subgroup G} (hBP : B ≤ P) (hBQ : B ≤ Q)
    (n : N) (g : G)
    (hPg : P ∈ restrictedApartment B π S g)
    (hQg : conjugateSubgroup (n : G) Q ∈ restrictedApartment B π S g) :
    restrictedApartment B π S
        (h.twoParabolicApartmentTransport hBP hBQ n g hPg hQg : G) =
      restrictedApartment B π S g :=
  (h.exists_mem_two_parabolics_restrictedApartment_eq hBP hBQ n g hPg hQg).choose_spec.2.2

end IsTitsSystem

end Langlands.Group
