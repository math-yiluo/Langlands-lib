import Langlands.ClassField.Global.CyclicHasseNormStatement
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.ClassField.Global.IdeleCoefficientSequence
import Langlands.ClassField.Global.IdeleGaloisDescentProof

/-! # The cyclic Hasse norm theorem for principal ideles -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory
open scoped NumberField BigOperators
open Langlands.Global.AdelicFunctoriality

universe u

private theorem ideleNorm_relativeIdeleAut {F E : Type u} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (d : IdeleGroup (𝓞 E) E) :
    ideleNorm (K := F) (relativeIdeleAut F E σ d) = ideleNorm (K := F) d := by
  classical
  let : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  apply (ideleGaloisDescent F E).1
  rw [ideleInclusion_ideleNorm_eq_prod, ideleInclusion_ideleNorm_eq_prod]
  apply Fintype.prod_equiv (Equiv.mulRight σ)
  intro τ
  change relativeIdeleAut F E τ (relativeIdeleAut F E σ d) =
    relativeIdeleAut F E (τ * σ) d
  rw [map_mul]
  rfl

/-- A field unit that is an idele norm is a field-unit norm in a cyclic extension. -/
theorem cyclicHasseNorm : CyclicHasseNormStatement.{u} := by
  classical
  intro F E _ _ _ _ _ _ _ a b hb
  let : CommGroup (E ≃ₐ[F] E) := IsCyclic.commGroup
  let : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  let cls := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E)
  have hcl : ideleClassNorm (K := F) (cls b) = 1 := by
    change (QuotientGroup.mk (ideleNorm (K := F) b) : IdeleClassGroup (𝓞 F) F) = 1
    rw [hb]
    exact (QuotientGroup.eq_one_iff _).2 ⟨a, rfl⟩
  let A := relativeIdeleClassRepresentation F E
  have hz : Additive.ofMul (cls b) ∈ LinearMap.ker A.norm.hom.toLinearMap := by
    change A.ρ.norm (Additive.ofMul (cls b)) = 0
    have hsum (a : A) : A.ρ.norm a = ∑ σ, A.ρ σ a := by
      rw [Representation.norm, LinearMap.sum_apply]
    refine (hsum _).trans ?_
    change ∑ σ : E ≃ₐ[F] E, Additive.ofMul (relativeIdeleClassAut F E σ (cls b)) = 0
    rw [← ofMul_prod, ← ideleClassNormGaloisProduct F E (cls b), hcl, map_one]
    rfl
  let z : LinearMap.ker A.norm.hom.toLinearMap := ⟨Additive.ofMul (cls b), hz⟩
  have hπ : Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 odd_one z = 0 :=
    (ideleClassH1Vanishing F E).elim _ _
  obtain ⟨c, hc⟩ := (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
    A g hg 1 odd_one z).mp hπ
  let c' := @Additive.toMul (IdeleClassGroup (𝓞 E) E) c
  have hclass : relativeIdeleClassAut F E g c' / c' = cls b := by
    change A.ρ g c - c = Additive.ofMul (cls b) at hc
    exact congrArg (@Additive.toMul (IdeleClassGroup (𝓞 E) E)) hc
  obtain ⟨d, hd⟩ := QuotientGroup.mk_surjective c'
  have hquot : cls (relativeIdeleAut F E g d / d) = cls b := by
    rw [map_div]
    change relativeIdeleClassAut F E g (QuotientGroup.mk d) / QuotientGroup.mk d = cls b
    rw [hd, hclass]
  let y := b / (relativeIdeleAut F E g d / d)
  have hy : cls y = 1 := by
    dsimp only [y]
    rw [map_div, hquot, div_self']
  obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff y).1 hy
  change IdeleGroup.unitEmbedding (𝓞 E) E x = y at hx
  have hxnorm : ideleNorm (K := F) (IdeleGroup.unitEmbedding (𝓞 E) E x) =
      IdeleGroup.unitEmbedding (𝓞 F) F a := by
    rw [hx]
    dsimp only [y]
    rw [map_div, map_div, ideleNorm_relativeIdeleAut, div_self', div_one, hb]
  rw [ideleNorm_principal] at hxnorm
  refine ⟨x, Units.ext (AdeleRing.algebraMap_injective (𝓞 F) F ?_)⟩
  exact congrArg Units.val hxnorm

end Langlands.ClassField.Global
