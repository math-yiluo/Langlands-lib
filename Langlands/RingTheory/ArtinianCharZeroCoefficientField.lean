import Langlands.GroupScheme.IntegralModel.EqualCharacteristicGreenberg.CoefficientField
import Mathlib.RingTheory.Artinian.Ring

/-! # Coefficient fields of local Artinian `ℚ`-algebras -/

universe u

open IsLocalRing

namespace Langlands.RingTheory

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]

/-- The maximal ideal of a local Artinian ring is nilpotent. -/
theorem isNilpotent_ker_residue : IsNilpotent (RingHom.ker (residue R)) := by
  rw [ker_residue, ← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact IsArtinianRing.isNilpotent_jacobson_bot

omit [IsArtinianRing R] in
/-- The residue field of a local `ℚ`-algebra has characteristic zero. -/
theorem charZero_residueField [Algebra ℚ R] : CharZero (ResidueField R) := by
  let : Algebra ℚ (ResidueField R) := ((residue R).comp (algebraMap ℚ R)).toAlgebra
  exact charZero_of_injective_algebraMap (algebraMap ℚ (ResidueField R)).injective

/-- A local Artinian `ℚ`-algebra has a coefficient field: a ring section of its residue map. -/
theorem exists_coefficientField [Algebra ℚ R] :
    ∃ σ : ResidueField R →+* R, (residue R).comp σ = RingHom.id _ := by
  have := charZero_residueField R
  have := GroupScheme.IntegralModel.formallySmooth_int_of_charZero (ResidueField R)
  let g : R →ₐ[ℤ] ResidueField R :=
    { toRingHom := residue R
      commutes' := fun z => by
        change residue R (algebraMap ℤ R z) = algebraMap ℤ _ z
        rw [eq_intCast (algebraMap ℤ R) z, eq_intCast (algebraMap ℤ (ResidueField R)) z,
          map_intCast] }
  have hg : Function.Surjective g := residue_surjective
  have hg' : IsNilpotent (RingHom.ker (g : R →+* ResidueField R)) := isNilpotent_ker_residue R
  let σ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id ℤ (ResidueField R)) g hg hg'
  refine ⟨σ.toRingHom, RingHom.ext fun x => ?_⟩
  exact Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id ℤ (ResidueField R)) g hg hg' x

end Langlands.RingTheory
