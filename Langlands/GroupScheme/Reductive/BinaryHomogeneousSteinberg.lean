import Langlands.GroupScheme.Reductive.BinarySteinbergRepresentation

/-! # Steinberg irreducibility on the actual binary homogeneous polynomial space -/

noncomputable section

universe u

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial Matrix

variable {R : Type u} [CommRing R]

/-- The binary monomial coordinates intertwine the actual homogeneous and coordinate actions. -/
theorem binaryBasis_equivFun_intertwining (m : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin 2) R)
    (f : homogeneousSubmodule (Fin 2) R m) :
    (binaryBasis m).equivFun (specialLinearRepresentation m g f) =
      binaryRepresentation m g ((binaryBasis m).equivFun f) := by
  rw [binaryRepresentation_apply]
  simp only [Module.Basis.equivFun_apply]
  change (binaryBasis m).repr (specialLinearRepresentation m g f) =
    LinearMap.toMatrix (binaryBasis m) (binaryBasis m)
      (specialLinearRepresentation m g) *ᵥ (binaryBasis m).repr f
  exact (LinearMap.toMatrix_mulVec_repr (binaryBasis m) (binaryBasis m) _ f).symm

/-- The actual binary homogeneous polynomial representation is equivalent to its monomial
coordinate representation in every degree. -/
def binaryHomogeneousEquiv (m : ℕ) :
    (specialLinearRepresentation (n := Fin 2) (S := R) m).Equiv
      (binaryRepresentation m) :=
  Representation.Equiv.mk (binaryBasis m).equivFun fun g => by
    apply LinearMap.ext
    intro f
    exact binaryBasis_equivFun_intertwining m g f

@[simp]
theorem binaryHomogeneousEquiv_apply (m : ℕ)
    (f : homogeneousSubmodule (Fin 2) R m) (c : Fin (m + 1)) :
    binaryHomogeneousEquiv m f c = (f : MvPolynomial (Fin 2) R).coeff (binaryExponent m c) :=
  rfl

section Field

variable {k : Type u} [Field k]

/-- The actual SL(2,k) action on the full homogeneous polynomial submodule of degree
p^s-1 is irreducible over every infinite field of prime characteristic p. -/
theorem binaryHomogeneous_isIrreducible (p : ℕ) [Fact p.Prime] [CharP k p] [Infinite k]
    (s : ℕ) :
    (specialLinearRepresentation (n := Fin 2) (S := k) (p ^ s - 1)).IsIrreducible := by
  have h := binaryRepresentation_isIrreducible (k := k) p s
  let e := binaryHomogeneousEquiv (R := k) (p ^ s - 1)
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.bijective).2 h

end Field

end Langlands.GroupScheme.HomogeneousPolynomial
