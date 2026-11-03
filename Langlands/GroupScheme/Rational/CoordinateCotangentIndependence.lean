import Langlands.GroupScheme.Rational.CoordinateCotangentWeights
import Mathlib.LinearAlgebra.DFinsupp

/-! # Independence of actual cotangent character spaces -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CoordinateWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

open Classical in
/-- Linear coordinate functionals separate the units of distinct characters. -/
theorem exists_characterCoefficient [IsAffineHom S.X.hom] (χ : characterLattice S) :
    ∃ L : CharacterUnits.Coord S.toGrp →ₗ[k] k,
      ∀ ψ : characterLattice S,
        L (CharacterUnits.unit ψ : CharacterUnits.Coord S.toGrp) =
          if ψ = χ then 1 else 0 := by
  classical
  let F := Finsupp.linearCombination k
    (fun ψ : characterLattice S => (CharacterUnits.unit ψ : CharacterUnits.Coord S.toGrp))
  have hF : LinearMap.ker F = ⊥ :=
    linearIndependent_iff_ker.mp (CharacterUnits.linearIndependent_unit (G := S.toGrp))
  refine ⟨(Finsupp.lapply χ).comp F.leftInverse, ?_⟩
  intro ψ
  have h := LinearMap.leftInverse_apply_of_inj hF (Finsupp.single ψ (1 : k))
  have h' := congrArg (fun f : characterLattice S →₀ k => f χ) h
  simpa [F, Finsupp.linearCombination_single, Finsupp.single_apply, eq_comm] using h'

/-- Distinct actual cotangent character eigenspaces are independent, without a
finite-dimensionality or splitness assumption. -/
theorem cotangentWeightSpace_iSupIndep [IsAffineHom S.X.hom]
    (b : AutomorphicAction S.toGrp G) :
    iSupIndep (cotangentWeightSpace b) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hsum χ hχ
  let A := CharacterUnits.Coord S.toGrp
  let s : Lie.AffinePoints S.toGrp A := CharacterUnits.universalPoint S.toGrp
  have ht : (∑ ψ ∈ t, (CharacterUnits.unit ψ : A) ⊗ₜ[k] v ψ) = 0 := by
    apply (cotangentTensorEquiv (G := G) A).injective
    simp only [map_sum, cotangentTensorEquiv_tmul, map_zero]
    calc
      (∑ ψ ∈ t, (CharacterUnits.unit ψ : A) • cotangentBaseChange (v ψ)) =
          ∑ ψ ∈ t, cotangentAction b s (cotangentBaseChange (v ψ)) := by
        apply Finset.sum_congr rfl
        intro ψ hψ
        have h := hv ψ hψ A s
        exact h.symm
      _ = cotangentAction b s (cotangentBaseChange (∑ ψ ∈ t, v ψ)) := by
        simp only [map_sum]
      _ = 0 := by rw [hsum, map_zero, map_zero]
  obtain ⟨L, hL⟩ := exists_characterCoefficient (S := S) χ
  have ht' := congrArg (fun z : A ⊗[k] Cotangent G =>
    TensorProduct.lid k (Cotangent G) ((L.rTensor (Cotangent G)) z)) ht
  simpa [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    hL, hχ] using ht'

end Langlands.GroupScheme.CoordinateWeights
