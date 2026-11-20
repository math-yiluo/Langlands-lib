import Langlands.Representation.Plancherel.UnitaryUnramifiedSmoothEvaluation
import Langlands.Representation.Plancherel.UnramifiedOperatorFamilies

/-! # Finite smooth expansions of regular operators on unitary tori -/

noncomputable section

open scoped NNReal ContDiff

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe uG uI uJ uV uW uB

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

set_option hygiene false in
local notation "χ" z => (⟨(e.symm z).val, (e.symm z).property.1⟩ : unramifiedCharacters ν)

/-- Scalar regular functions restrict to smooth functions in Laurent unitary
coordinates. -/
theorem isSmoothFiniteTorusFunction_unramifiedRegularFunction
    (he : HasLaurentUnitaryCoordinates ν e) (f : unramifiedRegularFunctions ν) :
    IsSmoothFiniteTorusFunction (fun z => f.val (χ z)) := by
  refine Algebra.adjoin_induction
    (p := fun a _ => (fun z => a (χ z)) ∈ smoothFiniteTorusFunctions J)
    ?_ ?_ ?_ ?_ f.property
  · rintro _ ⟨g, rfl⟩
    exact isSmoothFiniteTorusFunction_unitaryUnramified_evaluation ν e he g
  · intro c
    exact (smoothFiniteTorusFunctions J).algebraMap_mem c
  · intro a b ha hb hsa hsb
    exact (smoothFiniteTorusFunctions J).add_mem hsa hsb
  · intro a b ha hb hsa hsb
    exact (smoothFiniteTorusFunctions J).mul_mem hsa hsb

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Evaluate an operator numerator divided by its scalar denominator in the
unitary coordinates. -/
def unitaryRegularOperator
    (d : unramifiedRegularFunctions ν)
    (A : unramifiedCharacters ν → V →ₗ[ℂ] W) (z : J → Circle) : V →ₗ[ℂ] W :=
  (d.val (χ z))⁻¹ • A (χ z)

/-- After restriction to a finite-dimensional input submodule, a regular
operator has finitely many smooth scalar coefficients and fixed output
vectors. The same expansion works for every input vector. -/
theorem exists_unitaryRegularOperator_expansion
    (he : HasLaurentUnitaryCoordinates ν e)
    (d : unramifiedRegularFunctions ν) (hd : ∀ z : J → Circle, d.val (χ z) ≠ 0)
    (A : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (hA : IsPolynomialOperatorOn Set.univ (fun z => A z.val))
    {B : Type uB} [Fintype B] {E : Submodule ℂ V} (b : Module.Basis B ℂ E) :
    ∃ (N : B → ℕ) (c : ∀ i, Fin (N i) → smoothFiniteTorusFunctions J)
      (v : ∀ i, Fin (N i) → W) (ℓ : B → Module.Dual ℂ V),
      (∀ i (x : E), ℓ i x.val = b.coord i x) ∧
      ∀ (x : E) (z : J → Circle),
        unitaryRegularOperator ν e d A z x.val =
          ∑ i, ∑ j, (c i j).val z • ℓ i x.val • v i j := by
  classical
  choose N f v hv using fun i : B => hA (b i).val
  choose ℓ hℓ using fun i : B => (b.coord i).exists_extend
  have hdinv : IsSmoothFiniteTorusFunction (fun z => (d.val (χ z))⁻¹) :=
    (isSmoothFiniteTorusFunction_unramifiedRegularFunction ν e he d).inv
      (fun θ => hd (finiteTorusExp θ))
  let c (i : B) (j : Fin (N i)) : smoothFiniteTorusFunctions J :=
    ⟨fun z => (d.val (χ z))⁻¹ * (f i j).val (χ z),
      hdinv.mul (isSmoothFiniteTorusFunction_unramifiedRegularFunction ν e he (f i j))⟩
  have hcoord (i : B) (x : E) : ℓ i x.val = b.coord i x := LinearMap.congr_fun (hℓ i) x
  refine ⟨N, c, v, ℓ, hcoord, fun x z => ?_⟩
  have hx : ∑ i, (b.coord i x) • (b i).val = x.val := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply, Module.Basis.coord_apply]
      using congrArg E.subtype (b.sum_repr x)
  change (d.val (χ z))⁻¹ • A (χ z) x.val = _
  conv_lhs => rw [← hx, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hval : A (χ z) (b i).val = ∑ j, (f i j).val (χ z) • v i j :=
    hv i ⟨χ z, Set.mem_univ _⟩
  rw [map_smul, hval, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoord i x]
  simp only [c, smul_smul]
  congr 1
  ring

end Langlands.Plancherel
