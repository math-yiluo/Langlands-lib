import Langlands.GroupScheme.Torus.HermitianWeightIsotropy
import Langlands.GroupScheme.Torus.SignedWeightBasis
import Langlands.GroupScheme.Torus.SignedWeightCount

/-! # Assembling the signed support from the multiplicity bound -/

noncomputable section

namespace Langlands.GroupScheme.SignedWeightAssembly

open Module
open scoped BigOperators

variable {L : Type*} [AddCommGroup L]

/-- Membership in the finite signed support means being a basis vector or its negative. -/
theorem mem_signedWeights_iff {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (x : L) :
    x ∈ SignedWeightCount.signedWeights b ↔ ∃ j, x = b j ∨ x = -b j := by
  classical
  constructor
  · intro hx
    obtain ⟨⟨j, s⟩, _, h⟩ := Finset.mem_image.mp hx
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact ⟨j, Or.inl (by simpa [SignedWeightCount.signedWeight] using h.symm)⟩
    · exact ⟨j, Or.inr (by simpa [SignedWeightCount.signedWeight] using h.symm)⟩
  · rintro ⟨j, rfl | rfl⟩
    · apply Finset.mem_image.mpr
      exact ⟨(j, 1), Finset.mem_univ _, by simp [SignedWeightCount.signedWeight]⟩
    · apply Finset.mem_image.mpr
      exact ⟨(j, -1), Finset.mem_univ _, by simp [SignedWeightCount.signedWeight]⟩

variable [DecidableEq L]

/-- Signed representatives of a symmetric generating support, with the rank bound,
produce an exact signed integral basis support and multiplicity one on both signs. -/
theorem exists_basis_of_representatives (A P : Finset L) (d : L → ℕ) (r : ℕ)
    (hgen : AddSubgroup.closure (A : Set L) = ⊤)
    (hsym : ∀ x ∈ A, -x ∈ A) (hPA : P ⊆ A)
    (hcover : ∀ x ∈ A, x = 0 ∨ x ∈ P ∨ -x ∈ P)
    (hpos : ∀ x ∈ P, 0 < d x)
    (hbound : ∑ x ∈ P, d x ≤ r) (hrank : finrank ℤ L = r)
    (hneg : ∀ x ∈ P, d (-x) = d x) :
    ∃ b : Basis (Fin r) ℤ L,
      A.erase 0 = SignedWeightCount.signedWeights b ∧
      ∀ p, d (SignedWeightCount.signedWeight b p) = 1 := by
  classical
  have hbound' : ∑ x ∈ P, d x ≤ finrank ℤ L := by rwa [hrank]
  have hspan := SignedWeightBasis.span_eq_top_of_signed_support
    (A : Set L) P hgen hcover
  obtain ⟨hcard, hmult⟩ := SignedWeightBasis.card_eq_finrank_and_multiplicity_eq_one
    P d hspan hpos hbound'
  let e : P ≃ Fin r := P.equivFinOfCardEq (hcard.trans hrank)
  let b : Basis (Fin r) ℤ L :=
    (SignedWeightBasis.basisOfSignedSupport (A : Set L) P d hgen hcover hpos hbound').reindex e
  have hb : ∀ j, b j = (e.symm j : L) := by
    intro j
    simp only [b, Basis.reindex_apply, SignedWeightBasis.basisOfSignedSupport_apply]
  have hbrep : ∀ x (hx : x ∈ P), b (e ⟨x, hx⟩) = x := by
    intro x hx
    rw [hb, Equiv.symm_apply_apply]
  refine ⟨b, ?_, ?_⟩
  · ext x
    rw [Finset.mem_erase, mem_signedWeights_iff]
    constructor
    · rintro ⟨hx0, hxA⟩
      rcases hcover x hxA with hx | hx | hx
      · exact (hx0 hx).elim
      · exact ⟨e ⟨x, hx⟩, Or.inl (hbrep x hx).symm⟩
      · exact ⟨e ⟨-x, hx⟩, Or.inr (by rw [hbrep, neg_neg])⟩
    · rintro ⟨j, rfl | rfl⟩
      · exact ⟨b.ne_zero j, hb j ▸ hPA (e.symm j).property⟩
      · refine ⟨neg_ne_zero.mpr (b.ne_zero j), ?_⟩
        rw [hb]
        exact hsym _ (hPA (e.symm j).property)
  · rintro ⟨j, s⟩
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa only [SignedWeightCount.signedWeight, Units.val_one, one_smul, hb] using
        hmult (e.symm j) (e.symm j).property
    · simpa only [SignedWeightCount.signedWeight, Units.val_neg, Units.val_one,
        neg_one_smul, hb] using
        (hneg (e.symm j) (e.symm j).property).trans
          (hmult (e.symm j) (e.symm j).property)

section CoordinateLattice

variable {I : Type*} [Fintype I]

/-- Choose a nonopposite half of any finite coordinate support, retaining coverage
of every nonzero weight up to sign. -/
theorem exists_nonopposite_half (A : Finset (I → ℤ)) :
    ∃ P : Finset (I → ℤ), P ⊆ A ∧
      (∀ x ∈ P, ∀ y ∈ P, x + y ≠ 0) ∧
      ∀ x ∈ A, x = 0 ∨ x ∈ P ∨ -x ∈ P := by
  classical
  obtain ⟨s, hs, hcover⟩ :=
    HermitianWeights.exists_nonopposite_subfamily (fun x : A => (x : I → ℤ))
  refine ⟨s.image Subtype.val, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact hs a ha b hb
  · intro x hx
    rcases hcover ⟨x, hx⟩ with hz | ⟨j, hj, h | h⟩
    · exact Or.inl hz
    · right
      left
      exact Finset.mem_image.mpr ⟨j, hj, h.symm⟩
    · right
      right
      exact Finset.mem_image.mpr ⟨j, hj, by
        simpa only [neg_neg] using (congrArg Neg.neg h).symm⟩

/-- A symmetric generating support with symmetric positive multiplicities and a
rank bound on every nonopposite half is exactly a multiplicity-one signed basis. -/
theorem exists_basis_of_nonopposite_bound (A : Finset (I → ℤ))
    (d : (I → ℤ) → ℕ) (r : ℕ)
    (hgen : AddSubgroup.closure (A : Set (I → ℤ)) = ⊤)
    (hsym : ∀ x ∈ A, -x ∈ A)
    (hpos : ∀ x ∈ A, 0 < d x)
    (hneg : ∀ x ∈ A, d (-x) = d x)
    (hbound : ∀ P : Finset (I → ℤ), P ⊆ A →
      (∀ x ∈ P, ∀ y ∈ P, x + y ≠ 0) → ∑ x ∈ P, d x ≤ r)
    (hrank : Fintype.card I = r) :
    ∃ b : Basis (Fin r) ℤ (I → ℤ),
      A.erase 0 = SignedWeightCount.signedWeights b ∧
      ∀ p, d (SignedWeightCount.signedWeight b p) = 1 := by
  classical
  obtain ⟨P, hPA, hnonopp, hcover⟩ := exists_nonopposite_half A
  exact exists_basis_of_representatives A P d r hgen hsym hPA hcover
    (fun x hx => hpos x (hPA hx)) (hbound P hPA hnonopp)
    ((Module.finrank_fintype_fun_eq_card ℤ).trans hrank)
    (fun x hx => hneg x (hPA hx))

section ChosenBasis

variable (A : Finset (I → ℤ)) (d : (I → ℤ) → ℕ) (r : ℕ)
  (hgen : AddSubgroup.closure (A : Set (I → ℤ)) = ⊤)
  (hsym : ∀ x ∈ A, -x ∈ A)
  (hpos : ∀ x ∈ A, 0 < d x)
  (hneg : ∀ x ∈ A, d (-x) = d x)
  (hbound : ∀ P : Finset (I → ℤ), P ⊆ A →
    (∀ x ∈ P, ∀ y ∈ P, x + y ≠ 0) → ∑ x ∈ P, d x ≤ r)
  (hrank : Fintype.card I = r)

/-- Choose the integral basis supplied by the nonopposite multiplicity bound. -/
def basisOfNonoppositeBound : Basis (Fin r) ℤ (I → ℤ) :=
  (exists_basis_of_nonopposite_bound A d r hgen hsym hpos hneg hbound hrank).choose

/-- The chosen basis has the exact signed support and multiplicity-one properties. -/
theorem basisOfNonoppositeBound_spec :
    A.erase 0 = SignedWeightCount.signedWeights
      (basisOfNonoppositeBound A d r hgen hsym hpos hneg hbound hrank) ∧
    ∀ p, d (SignedWeightCount.signedWeight
      (basisOfNonoppositeBound A d r hgen hsym hpos hneg hbound hrank) p) = 1 :=
  (exists_basis_of_nonopposite_bound A d r hgen hsym hpos hneg hbound hrank).choose_spec

end ChosenBasis

end CoordinateLattice

end Langlands.GroupScheme.SignedWeightAssembly
