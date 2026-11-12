import Langlands.Representation.Intertwining.PQKernelCharacters
import Langlands.Representation.Exponents.CentralDecompositionAlgebra

/-! # Spectral regularity for finite action algebras -/

noncomputable section

namespace Langlands.PQFiniteActionRegularity

open CentralDecomposition

variable {B : Type*} [CommGroup B]
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The faithful commutative algebra of an action, as an actual quotient. -/
abbrev actionQuotient (ρ : Representation ℂ B V) :=
  MonoidAlgebra ℂ B ⧸ groupAlgebraKernel ρ (MonoidHom.id B)

/-- Finiteness of the actual operator span gives a finite-dimensional action
quotient, even when the representation carrier is infinite-dimensional. -/
theorem finite_actionQuotient_of_finite_span (ρ : Representation ℂ B V)
    [Module.Finite ℂ (Submodule.span ℂ (Set.range ρ))] :
    Module.Finite ℂ (actionQuotient ρ) := by
  let S := Submodule.span ℂ (Set.range ρ)
  have hmem (c : MonoidAlgebra ℂ B) : Representation.asAlgebraHom ρ c ∈ S := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simpa only [map_zero] using S.zero_mem
    | add a b ha hb => simpa only [map_add] using S.add_mem ha hb
    | single b z =>
      rw [Representation.asAlgebraHom_single]
      exact S.smul_mem z (Submodule.subset_span ⟨b, rfl⟩)
  let ι : actionQuotient ρ →ₐ[ℂ] Module.End ℂ V :=
    Ideal.kerLiftAlg (Representation.asAlgebraHom ρ)
  let f : actionQuotient ρ →ₗ[ℂ] S := ι.toLinearMap.codRestrict S (by
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hmem c)
  have hf : Function.Injective f := by
    intro x y hxy
    exact Ideal.kerLiftAlg_injective (Representation.asAlgebraHom ρ)
      (congrArg Subtype.val hxy)
  exact Module.Finite.of_injective f hf

/-- Every scalar character of a finite-dimensional faithful action algebra
occurs as a generalized group character. -/
theorem generalizedCharacter_of_faithful_algebra
    {R : Type*} [CommRing R] [Algebra ℂ R] [Module.Finite ℂ R]
    (ρ : Representation ℂ B V) (ι : R →ₐ[ℂ] Module.End ℂ V)
    (hιinj : Function.Injective ι) (τ : B →* R)
    (hι : ∀ b, ι (τ b) = ρ b) (ψ : R →ₐ[ℂ] ℂ) :
    IsGeneralizedEigencharacter ρ (algebraCharacter τ ψ) := by
  classical
  let : Finite (R →ₐ[ℂ] ℂ) := finite_algHom
  let : Fintype (R →ₐ[ℂ] ℂ) := Fintype.ofFinite _
  obtain ⟨N, h, hu, hann⟩ := exists_decomposition (K := ℂ) (R := R)
  have hother (φ : R →ₐ[ℂ] ℂ) (hφ : φ ≠ ψ) : ψ (h φ) = 0 := by
    obtain ⟨r, hrψ, hrφ⟩ := exists_separating ψ φ hφ.symm
    have hr : r ∈ RingHom.ker φ := RingHom.mem_ker.mpr hrφ
    have he := congrArg ψ (hann φ _ (Ideal.pow_mem_pow hr N))
    simpa only [map_mul, map_pow, hrψ, one_pow, one_mul, map_zero] using he
  have hhψ : ψ (h ψ) ≠ 0 := by
    have hsum : ψ (∑ φ, h φ) ≠ 0 := (hu.map ψ).ne_zero
    rw [map_sum, Finset.sum_eq_single ψ] at hsum
    · exact hsum
    · intro φ _ hφ
      exact hother φ hφ
    · intro hψ
      exact (hψ (Finset.mem_univ ψ)).elim
  have hh : ι (h ψ) ≠ 0 := by
    intro hz
    have h0 : h ψ = 0 := hιinj (hz.trans (map_zero ι).symm)
    exact hhψ (h0 ▸ map_zero ψ)
  obtain ⟨v, hv⟩ : ∃ v : V, ι (h ψ) v ≠ 0 := by
    by_contra! hz
    exact hh (LinearMap.ext hz)
  apply (isGeneralizedEigencharacter_iff ρ _).mpr
  refine ⟨N, ι (h ψ) v, hv, ?_⟩
  intro b
  have hdef : ρ b - (algebraCharacter τ ψ b : ℂ) • 1 =
      ι (τ b - algebraMap ℂ R (ψ (τ b))) := by
    rw [map_sub, AlgHom.commutes, hι, Algebra.algebraMap_eq_smul_one,
      algebraCharacter_apply]
  have hk : τ b - algebraMap ℂ R (ψ (τ b)) ∈ RingHom.ker ψ := by
    simp [RingHom.mem_ker]
  rw [hdef, ← map_pow, ← Module.End.mul_apply, ← map_mul,
    hann ψ _ (Ideal.pow_mem_pow hk N), map_zero, LinearMap.zero_apply]

/-- A character of the actual finite action quotient occurs in the action. -/
theorem generalizedCharacter_of_actionQuotient
    (ρ : Representation ℂ B V) [Module.Finite ℂ (actionQuotient ρ)]
    (ψ : actionQuotient ρ →ₐ[ℂ] ℂ) :
    IsGeneralizedEigencharacter ρ
      (algebraCharacter
        ((Ideal.Quotient.mk (groupAlgebraKernel ρ (MonoidHom.id B))).toMonoidHom.comp
          (MonoidAlgebra.of ℂ B)) ψ) := by
  let ι := Ideal.kerLiftAlg (Representation.asAlgebraHom ρ)
  have : Module.Finite ℂ (MonoidAlgebra ℂ B ⧸ RingHom.ker (Representation.asAlgebraHom ρ)) :=
    ‹Module.Finite ℂ (actionQuotient ρ)›
  exact generalizedCharacter_of_faithful_algebra ρ ι
    (Ideal.kerLiftAlg_injective _) _ (fun b => by
      change Representation.asAlgebraHom ρ (MonoidAlgebra.of ℂ B b) = ρ b
      exact Representation.asAlgebraHom_of ρ b) ψ

/-- For finite action quotients, disjoint generalized-character sets are
equivalent to comaximal action kernels. -/
theorem sup_kernels_eq_top_iff
    (ρ : Representation ℂ B V) (σ : Representation ℂ B W)
    [Module.Finite ℂ (actionQuotient ρ)] [Module.Finite ℂ (actionQuotient σ)] :
    groupAlgebraKernel ρ (MonoidHom.id B) ⊔
        groupAlgebraKernel σ (MonoidHom.id B) = ⊤ ↔
      Disjoint {χ | IsGeneralizedEigencharacter ρ χ}
        {χ | IsGeneralizedEigencharacter σ χ} := by
  constructor
  · exact PQKernelCharacters.disjoint_generalizedCharacters ρ σ
  · intro hdisjoint
    by_contra htop
    let I := groupAlgebraKernel ρ (MonoidHom.id B)
    let J := groupAlgebraKernel σ (MonoidHom.id B)
    let S := MonoidAlgebra ℂ B ⧸ (I ⊔ J)
    have : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr htop
    let fρ : actionQuotient ρ →ₐ[ℂ] S := Ideal.Quotient.factorₐ ℂ le_sup_left
    let fσ : actionQuotient σ →ₐ[ℂ] S := Ideal.Quotient.factorₐ ℂ le_sup_right
    have hfρ : Function.Surjective fρ := Ideal.Quotient.factor_surjective le_sup_left
    have : Module.Finite ℂ S := Module.Finite.of_surjective fρ.toLinearMap hfρ
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := S)
    let := hm
    obtain ⟨ψ, -⟩ := exists_algHom_ker_eq (K := ℂ) m
    have hρ := generalizedCharacter_of_actionQuotient ρ (ψ.comp fρ)
    have hσ := generalizedCharacter_of_actionQuotient σ (ψ.comp fσ)
    have he : algebraCharacter
        ((Ideal.Quotient.mk I).toMonoidHom.comp (MonoidAlgebra.of ℂ B)) (ψ.comp fρ) =
        algebraCharacter
        ((Ideal.Quotient.mk J).toMonoidHom.comp (MonoidAlgebra.of ℂ B)) (ψ.comp fσ) := by
      apply MonoidHom.ext
      intro b
      apply Units.ext
      rfl
    exact Set.disjoint_left.mp hdisjoint hρ (he ▸ hσ)

end Langlands.PQFiniteActionRegularity
