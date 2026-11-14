import Langlands.GroupScheme.Torus.SignedWeightAssembly
import Langlands.GroupScheme.Torus.SignedWeightTransport

/-! # A character basis and weight formula from an independent row decomposition -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped BigOperators

namespace Langlands.GroupScheme.SignedWeightCharacterBasis

variable {K : Type u} [Field K] {I : Type u} [Fintype I]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}

section Basis

variable (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (A : Finset (I → ℤ)) (d : (I → ℤ) → ℕ) (r : ℕ)
  (hgen : AddSubgroup.closure (A : Set (I → ℤ)) = ⊤)
  (hsym : ∀ m ∈ A, -m ∈ A) (hpos : ∀ m ∈ A, 0 < d m)
  (hneg : ∀ m ∈ A, d (-m) = d m)
  (hbound : ∀ P : Finset (I → ℤ), P ⊆ A →
    (∀ m ∈ P, ∀ p ∈ P, m + p ≠ 0) → ∑ m ∈ P, d m ≤ r)
  (hrank : Fintype.card I = r)

/-- The actual character basis supplied by a signed coordinate multiplicity bound. -/
def characterBasisOfNonoppositeBound : Basis (Fin r) ℤ (characterLattice S) :=
  SignedWeightTransport.characterBasis e
    (SignedWeightAssembly.basisOfNonoppositeBound
      A d r hgen hsym hpos hneg hbound hrank)

end Basis

section Decomposition

variable {D V : Type*} [DivisionRing D] [AddCommGroup V] [Module D V]
  [FiniteDimensional D V]

/-- An independent spanning row decomposition with faithful signed support,
opposite multiplicity equality, the nonopposite bound and coordinate rank `r`
gives actual independent characters detecting cocharacters and the signed count
for every family obtained by grouping the row spaces by the character pairing. -/
theorem exists_characters_of_decomposition
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (A : Finset (I → ℤ)) (W : (I → ℤ) → Submodule D V) (r : ℕ)
    (hW : iSupIndep W) (hspan : (⨆ m ∈ A, W m) = ⊤)
    (hsupport : ∀ m, W m ≠ ⊥ ↔ m ∈ A)
    (hgen : AddSubgroup.closure (A : Set (I → ℤ)) = ⊤)
    (hneg : ∀ m ∈ A, finrank D (W (-m)) = finrank D (W m))
    (hbound : ∀ P : Finset (I → ℤ), P ⊆ A →
      (∀ m ∈ P, ∀ p ∈ P, m + p ≠ 0) → ∑ m ∈ P, finrank D (W m) ≤ r)
    (hrank : Fintype.card I = r)
    (F : cocharacterLattice S → ℤ → Submodule D V)
    (hgroup : ∀ ν c, F ν c = ⨆ m ∈ A.filter
      (fun m => latticePairing S (SignedWeightTransport.characterEquiv e m) ν = c), W m) :
    ∃ χ : Fin r → characterLattice S,
      LinearIndependent ℤ χ ∧
      (∀ ν : cocharacterLattice S, (∀ j, latticePairing S (χ j) ν = 0) → ν = 0) ∧
      ∀ (ν : cocharacterLattice S) (c : ℤ),
        finrank D (F ν c) =
          Nat.card {p : Fin r × ℤˣ // (p.2 : ℤ) * latticePairing S (χ p.1) ν = c} +
            if c = 0 then finrank D V - 2 * r else 0 := by
  classical
  let d : (I → ℤ) → ℕ := fun m => finrank D (W m)
  have hpos : ∀ m ∈ A, 0 < d m := by
    intro m hm
    exact Submodule.one_le_finrank_iff.mpr ((hsupport m).mpr hm)
  have hsym : ∀ m ∈ A, -m ∈ A := by
    intro m hm
    apply (hsupport (-m)).mp
    apply Submodule.one_le_finrank_iff.mp
    rw [hneg m hm]
    exact hpos m hm
  let b := SignedWeightAssembly.basisOfNonoppositeBound
    A d r hgen hsym hpos hneg hbound hrank
  have hspec := SignedWeightAssembly.basisOfNonoppositeBound_spec
    A d r hgen hsym hpos hneg hbound hrank
  let B := characterBasisOfNonoppositeBound e A d r hgen hsym hpos hneg hbound hrank
  refine ⟨B, B.linearIndependent, ?_, ?_⟩
  · exact SignedWeightTransport.characterBasis_detects_cocharacters e b
  · intro ν c
    rw [hgroup]
    have hzero : 0 ∉ A → W 0 = ⊥ := by
      intro h0
      by_contra h
      exact h0 ((hsupport 0).mp h)
    have h := SignedWeightTransport.finrank_eq_signed_card_add_residual
      e A b W hW hspan hspec.1 hzero hspec.2 ν c
    simpa only [B, characterBasisOfNonoppositeBound, b, Fintype.card_fin] using h

end Decomposition

end Langlands.GroupScheme.SignedWeightCharacterBasis
