import Langlands.Shimura.Unitary.ComplexWeightConjugacy

noncomputable section
open Matrix Module
open scoped Classical

namespace Langlands.Shimura.ComplexMatrix
variable {S : Type*} [CommRing S] (s : S ≃+* S) (n : ℕ)

local instance : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s

local instance : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.symm s.toRingHom s.symm.toRingHom

/-- Apply a coefficient automorphism to every coordinate of a vector. -/
def coefficientVectorEquiv : (Fin n → S) ≃ₛₗ[s.toRingHom] (Fin n → S) where
  toFun v j := s (v j)
  invFun v j := s.symm (v j)
  left_inv v := funext fun j => s.symm_apply_apply (v j)
  right_inv v := funext fun j => s.apply_symm_apply (v j)
  map_add' v w := funext fun j => map_add s (v j) (w j)
  map_smul' c v := funext fun j => map_mul s c (v j)

/-- Semilinear coordinate change intertwines matrix multiplication on vectors. -/
theorem coefficientVectorEquiv_mulVec (M : Matrix (Fin n) (Fin n) S) (v : Fin n → S) :
    coefficientVectorEquiv s n (M *ᵥ v) = M.map s *ᵥ coefficientVectorEquiv s n v :=
  funext fun j => RingHom.map_mulVec s.toRingHom M v j

variable {n} (a : Sˣ → Matrix (Fin n) (Fin n) S)

/-- Transport coefficients and precompose the unit parameter by the inverse automorphism. -/
def coefficientWeightFamily (u : Sˣ) : Matrix (Fin n) (Fin n) S :=
  (a ((Units.mapEquiv s.toMulEquiv).symm u)).map s

/-- At a transported unit the matrix is the entrywise transport of the original matrix. -/
theorem coefficientWeightFamily_map (u : Sˣ) :
    coefficientWeightFamily s a (Units.mapEquiv s.toMulEquiv u) = (a u).map s := by
  simp only [coefficientWeightFamily, MulEquiv.symm_apply_apply]

/-- Semilinear coefficient transport preserves the common inverse-weight condition. -/
theorem mem_inverseWeightSpace_coefficient_iff (v : Fin n → S) :
    coefficientVectorEquiv s n v ∈ inverseWeightSpace (coefficientWeightFamily s a) ↔
      v ∈ inverseWeightSpace a := by
  constructor
  · intro hv u
    apply (coefficientVectorEquiv s n).injective
    rw [coefficientVectorEquiv_mulVec]
    have h := hv (Units.mapEquiv s.toMulEquiv u)
    rw [coefficientWeightFamily_map] at h
    exact h.trans (by ext j; exact (map_mul s (↑(u⁻¹) : S) (v j)).symm)
  · intro hv u
    obtain ⟨w, rfl⟩ := (Units.mapEquiv s.toMulEquiv).surjective u
    rw [coefficientWeightFamily_map, ← coefficientVectorEquiv_mulVec, hv w]
    ext j
    exact map_mul s (↑(w⁻¹) : S) (v j)

/-- The induced semilinear equivalence between actual inverse-weight submodules. -/
def inverseWeightSpaceCoefficientEquiv :
    inverseWeightSpace a ≃ₛₗ[s.toRingHom]
      inverseWeightSpace (coefficientWeightFamily s a) where
  toFun v := ⟨coefficientVectorEquiv s n v,
    (mem_inverseWeightSpace_coefficient_iff s a v).mpr v.property⟩
  invFun w := ⟨(coefficientVectorEquiv s n).symm w,
    (mem_inverseWeightSpace_coefficient_iff s a ((coefficientVectorEquiv s n).symm w)).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using w.property)⟩
  left_inv v := Subtype.ext ((coefficientVectorEquiv s n).symm_apply_apply v)
  right_inv w := Subtype.ext ((coefficientVectorEquiv s n).apply_symm_apply w)
  map_add' v w := Subtype.ext ((coefficientVectorEquiv s n).map_add v w)
  map_smul' c v := Subtype.ext ((coefficientVectorEquiv s n).map_smulₛₗ c v)

/-- Inverse-weight rank is invariant under semilinear coefficient transport. -/
theorem finrank_inverseWeightSpace_coefficient :
    Module.finrank S (inverseWeightSpace (coefficientWeightFamily s a)) =
      Module.finrank S (inverseWeightSpace a) := by
  have h := rank_eq_of_equiv_equiv s
    (inverseWeightSpaceCoefficientEquiv s a).toAddEquiv s.bijective
    (fun c v => (inverseWeightSpaceCoefficientEquiv s a).map_smulₛₗ c v)
  exact (congrArg Cardinal.toNat h).symm

end Langlands.Shimura.ComplexMatrix
