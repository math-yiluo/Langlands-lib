import Langlands.Representation.IntegerLattice.GeneralizedWeightBlockBasisStatement
import Langlands.LinearAlgebra.CommutingNilpotentStrictUpperBasisProof

/-! # A common triangular basis for the actual generalized-weight blocks -/

set_option autoImplicit false

universe u

namespace Langlands.IntegerLattice

variable {d : ℕ} {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The actual restricted generators commute. -/
theorem generalizedWeightBlockGenerator_commute
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (s t : Fin d) :
    Commute
      (generalizedWeightBlockGenerator A c s : Module.End ℂ (generalizedWeightBlock A c))
      (generalizedWeightBlockGenerator A c t : Module.End ℂ (generalizedWeightBlock A c)) := by
  rw [coe_generalizedWeightBlockGenerator, coe_generalizedWeightBlockGenerator]
  exact (Commute.all (generator d s) (generator d t)).map
    (generalizedWeightBlockRepresentation A c)

/-- Scalar normalization and subtraction of the identity preserve commutation. -/
theorem normalizedGeneratorDifference_commute
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (s t : Fin d) :
    Commute (normalizedGeneratorDifference A c s) (normalizedGeneratorDifference A c t) := by
  unfold normalizedGeneratorDifference
  rw [coe_normalizedBlockGenerator, coe_normalizedBlockGenerator]
  exact (((generalizedWeightBlockGenerator_commute A c s t).smul_left
    (c s : ℂ)⁻¹).smul_right (c t : ℂ)⁻¹).sub_left (Commute.one_left _)
      |>.sub_right (Commute.one_right _)

/-- On the actual block, each normalized generator difference is nilpotent. -/
theorem normalizedGeneratorDifference_isNilpotent [FiniteDimensional ℂ V]
    (A : CommutingInvertibleTuple d V) (c : Fin d → ℂˣ) (t : Fin d) :
    IsNilpotent (normalizedGeneratorDifference A c t) := by
  let f : Module.End ℂ V := A.1 t
  have hW : Set.MapsTo (f - (c t : ℂ) • (1 : Module.End ℂ V))
      ↑(generalizedWeightBlock A c) ↑(generalizedWeightBlock A c) := by
    intro v hv
    apply (generalizedWeightBlock A c).sub_mem
    · change (A.1 t : Module.End ℂ V) v ∈
        (generalizedWeightBlock A c : Set V)
      rw [← tupleRepresentationEquiv_generator]
      exact mapsTo_generalizedWeightBlock A c (generator d t) hv
    · exact (generalizedWeightBlock A c).smul_mem (c t : ℂ) hv
  have hn : IsNilpotent ((f - (c t : ℂ) • 1).restrict hW) :=
    Module.End.isNilpotent_restrict_of_le
      (fun v hv => mem_generalizedWeightBlock.mp hv t)
      (f.isNilpotent_restrict_genEigenspace_top (c t : ℂ))
  have heq : normalizedGeneratorDifference A c t =
      (c t : ℂ)⁻¹ • ((f - (c t : ℂ) • 1).restrict hW) := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [normalizedGeneratorDifference_apply_coe]
    change (c t : ℂ)⁻¹ • f (w : V) - (w : V) =
      (c t : ℂ)⁻¹ • ((f - (c t : ℂ) • 1) (w : V))
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      smul_sub, smul_smul, inv_mul_cancel₀ (c t).ne_zero, one_smul]
  rw [heq]
  exact hn.smul (c t : ℂ)⁻¹

end Langlands.IntegerLattice

namespace Langlands

open IntegerLattice

/-- One basis simultaneously gives the five claimed formulas on each actual block. -/
theorem commutingTupleGeneralizedWeightBlockBasis :
    CommutingTupleGeneralizedWeightBlockBasisStatement.{u} := by
  classical
  intro d V _ _ _ A c
  obtain ⟨b, hb⟩ :=
    CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis
      ℂ (generalizedWeightBlock A c) (Fin d) (normalizedGeneratorDifference A c)
      (normalizedGeneratorDifference_commute A c)
      (normalizedGeneratorDifference_isNilpotent A c)
  have hcoord : ∀ t i j,
      b.repr ((generalizedWeightBlockGenerator A c t :
        Module.End ℂ (generalizedWeightBlock A c)) (b j)) i =
          (c t : ℂ) * ((if i = j then 1 else 0) +
            b.repr (normalizedGeneratorDifference A c t (b j)) i) := by
    intro t i j
    rw [generalizedWeightBlockGenerator_eq_smul]
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
      map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul,
      Module.Basis.repr_self_apply, eq_comm]
  refine ⟨b, hb, generalizedWeightBlockGenerator_eq_smul A c, hcoord, ?_, ?_⟩
  · intro t i j hij
    rw [hcoord, hb t i j (le_of_lt hij), ite_eq_right (ne_of_gt hij)]
    simp
  · intro t i
    rw [hcoord, hb t i i le_rfl, ite_eq_left rfl]
    simp

end Langlands
