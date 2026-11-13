import Langlands.GroupScheme.Descent.AutomorphismTensor
import Langlands.Galois.Local.SeparableUnramifiedFiniteArithmetic
import Langlands.Galois.Local.SeparableUnramifiedGaloisProof

/-! # The integer tensor decomposition at a finite unramified stage -/

noncomputable section

universe u

open IsLocalRing
open scoped ValuativeRel TensorProduct

namespace Langlands.GroupScheme.Descent.FiniteUnramified

open Langlands.LocalGalois Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

variable (E : IntermediateField F (SeparableClosure F))
    [FiniteDimensional F E] [IsGalois F E]

/-- At a finite unramified Galois stage the actual residue action is bijective. -/
theorem unramified_residueHom_bijective (hE : ArithmeticUnramified F E) :
    Function.Bijective (residueHom F E) := by
  let : IsGalois (ResidueField (baseIntegers F))
      (ResidueField (extensionIntegers F E)) := isGalois_of_finite_base _ _
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  refine ⟨residueHom_surjective F E, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    (arithmeticUnramified_iff_residue_finrank F E).mp hE]

/-- Distinct field automorphisms have a unit difference on some integer. -/
theorem integerAut_unit_separated (hE : ArithmeticUnramified F E)
    (σ τ : E ≃ₐ[F] E) (hστ : σ ≠ τ) :
    ∃ b : extensionIntegers F E,
      IsUnit (integerAut F E σ b - integerAut F E τ b) := by
  have hn : residueHom F E σ ≠ residueHom F E τ :=
    fun h => hστ ((unramified_residueHom_bijective F E hE).injective h)
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hn
  obtain ⟨b, rfl⟩ := residue_surjective x
  refine ⟨b, (residue_ne_zero_iff_isUnit _).mp ?_⟩
  simpa only [map_sub, sub_ne_zero, ← residueHom_apply] using hx

/-- The canonical integral tensor equivalence, indexed by the actual field
automorphisms. -/
def integerTensorEquiv (hE : ArithmeticUnramified F E) :
    (extensionIntegers F E ⊗[baseIntegers F] extensionIntegers F E) ≃ₐ[
      extensionIntegers F E] ((E ≃ₐ[F] E) → extensionIntegers F E) :=
  AutomorphismTensor.equiv (baseIntegers F) (extensionIntegers F E)
    (integerAut F E) (integerAut_unit_separated F E hE)
    ((IsGalois.card_aut_eq_finrank F E).trans (spectralIntegers_finrank F E).symm)

@[simp]
theorem integerTensorEquiv_tmul (hE : ArithmeticUnramified F E)
    (a b : extensionIntegers F E) (σ : E ≃ₐ[F] E) :
    integerTensorEquiv F E hE (a ⊗ₜ[baseIntegers F] b) σ =
      a * integerAut F E σ b := rfl

end Langlands.GroupScheme.Descent.FiniteUnramified
