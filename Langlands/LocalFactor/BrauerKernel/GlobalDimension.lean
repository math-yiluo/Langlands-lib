import Langlands.LocalFactor.BrauerKernel.GlobalRelation
import Langlands.Representation.Finite.InducedCharacterProof

/-! # The dimension identity for a globalized Galois type relation -/

noncomputable section

universe uF u

namespace Langlands.LocalFactor.NonabelianBrauer

open CommonClosure VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {e : ReciprocityFamily F}
  {z : Presentation F (Correspondence.baseExtension F)}
  (D : GaloisTypeDecomposition F e z)
  (k K' : Type u) [Field k] [NumberField k] [Field K'] [NumberField K']
  [Algebra k K'] [IsGalois k K']
  (θ : (K' ≃ₐ[k] K') ≃* (D.K.field ≃ₐ[F.Carrier] D.K.field))

/-- The integer virtual dimension in a fixed type, weighted by the global field degrees. -/
def globalTypeDimension (τ : ℂ) : ℤ := by
  classical
  exact ∑ g ∈ z.support, z g * (Module.finrank k (globalField D k K' θ g) : ℤ) *
    ((if D.t₁ g = τ then 1 else 0) - (if D.t₂ g = τ then 1 else 0))

/-- The global field degree is the index of the corresponding local Galois image. -/
theorem finrank_globalField_eq_galoisImage_index
    (g : Generator F (Correspondence.baseExtension F)) :
    Module.finrank k (globalField D k K' θ g) =
      (@galoisImage p _ F D.K D.normal g.extension).index := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index]
  change (IntermediateField.fixedField (globalSubgroup D k K' θ g)).fixingSubgroup.index = _
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact Subgroup.index_comap_of_surjective _ θ.surjective

/-- Each type has virtual dimension zero in the finite local Galois relation. -/
theorem galoisType_dimension (τ : ℂ) :
    ∑ g ∈ z.support, z g * ((@galoisImage p _ F D.K D.normal g.extension).index : ℤ) *
      ((if D.t₁ g = τ then 1 else 0) - (if D.t₂ g = τ then 1 else 0)) = 0 := by
  classical
  let G := D.K.field ≃ₐ[F.Carrier] D.K.field
  let : Fintype G := Fintype.ofFinite G
  have hdim (H : Subgroup G) (χ : H →* ℂˣ) :
      FiniteRep.virtualCharacter (k := ℂ) (G := G)
          (FiniteRep.ofClass (FiniteRep.induce H
            (FiniteRep.classOf (FiniteRep.oneDimensional χ)))) 1 =
        (H.index : ℂ) := by
    rw [FiniteRep.virtualCharacter_ofClass]
    change (FiniteRep.induceRep H (FiniteRep.oneDimensional χ)).character 1 = _
    rw [FDRep.char_one, FiniteRep.InducedCharacter.inducedDegree G H,
      FiniteRep.oneDimensional_finrank, mul_one]
  have htrace := congrArg
    (fun x => FiniteRep.virtualCharacter (k := ℂ) (G := G) x 1) (D.identity τ)
  have hsum :
      ∑ g ∈ z.support, (z g : ℂ) *
        ((@galoisImage p _ F D.K D.normal g.extension).index : ℂ) *
        ((if D.t₁ g = τ then 1 else 0) - (if D.t₂ g = τ then 1 else 0)) = 0 := by
    simp only [map_sum, Finset.sum_apply, map_zsmul, Pi.smul_apply, map_sub,
      Pi.sub_apply, map_zero, Pi.zero_apply] at htrace
    refine Eq.trans ?_ htrace
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [zsmul_eq_mul]
    split_ifs <;> simp_all
  exact_mod_cast hsum

/-- The global intermediate-field degrees have zero weighted dimension in every type. -/
theorem globalField_type_dimension (τ : ℂ) :
    ∑ g ∈ z.support, z g * (Module.finrank k (globalField D k K' θ g) : ℤ) *
      ((if D.t₁ g = τ then 1 else 0) - (if D.t₂ g = τ then 1 else 0)) = 0 := by
  simp_rw [finrank_globalField_eq_galoisImage_index D k K' θ]
  exact galoisType_dimension D τ

/-- Every type of the globalized Galois relation has virtual dimension zero. -/
theorem globalTypeDimension_eq_zero (τ : ℂ) :
    globalTypeDimension D k K' θ τ = 0 :=
  globalField_type_dimension D k K' θ τ

end Langlands.LocalFactor.NonabelianBrauer
